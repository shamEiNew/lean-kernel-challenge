import Spec

namespace Submission

/-
Direct Nat arithmetic variant; the doubling formulas and recursion are unchanged.
We store

    (F n, F (n - 1))

for n > 0.

If
    a = F n
    c = F (n - 1),

then

    F (2n)     = a * (a + c + c)
    F (2n - 1) = a*a + c*c

Hence, putting

    x = F (2n)
    y = F (2n - 1),

the next binary digit gives

    bit 0 : (x,     y)
    bit 1 : (x + y, x)

because F(2n+1) = F(2n) + F(2n-1).

The computational path therefore uses only:
  * 3 big multiplications per level
  * additions
  * no big Nat subtraction
  * no exponentiation
-/

/-- Subtraction-free doubling worker.

For positive `n ≤ fuel`,
`fdPrev fuel n = (F n, F (n-1))`.
-/
def fdPrev : Nat → Nat → Nat × Nat
  | 0, _ => (0, 0)
  | _ + 1, 0 => (0, 0)
  | _ + 1, 1 => (1, 0)
  | fuel + 1, n + 2 =>
      match fdPrev fuel ((n + 2) / 2) with
      | (a, c) =>
          let x := Nat.mul a (Nat.add (Nat.add a c) c)
          let y := Nat.add (Nat.mul a a) (Nat.mul c c)
          if (n + 2) % 2 = 0 then
            (x, y)
          else
            (Nat.add x y, x)

/--
Subtraction-free form of the even Fibonacci doubling identity:

    F(2m) = F(m) * (F(m) + 2 F(m-1)).
-/
theorem fib_even_prev (m : Nat) (hm : 0 < m) :
    Nat.fib (2 * m)
      =
    Nat.fib m *
      (Nat.fib m + Nat.fib (m - 1) + Nat.fib (m - 1)) := by
  rw [Nat.fib_two_mul]
  have hrec :
      Nat.fib (m + 1) =
        Nat.fib (m - 1) + Nat.fib m :=
    Nat.fib_add_one (Nat.ne_of_gt hm)
  rw [hrec]
  congr 1
  omega

/--
Odd predecessor identity:

    F(2m-1) = F(m)^2 + F(m-1)^2.
-/
theorem fib_odd_prev (m : Nat) (hm : 0 < m) :
    Nat.fib (2 * m - 1)
      =
    Nat.fib m * Nat.fib m
      +
    Nat.fib (m - 1) * Nat.fib (m - 1) := by
  have h := Nat.fib_two_mul_add_one (m - 1)
  have hm1 : m - 1 + 1 = m := by omega
  have hind : 2 * (m - 1) + 1 = 2 * m - 1 := by omega
  rw [hm1, hind] at h
  simpa [pow_two] using h

/--
Correctness invariant for `fdPrev`.
-/
theorem fdPrev_spec :
    (fuel n : Nat) →
    0 < n →
    n ≤ fuel →
    fdPrev fuel n = (Nat.fib n, Nat.fib (n - 1))
  | 0, n, hpos, hle => by
      omega
  | fuel + 1, 0, hpos, hle => by
      omega
  | fuel + 1, 1, hpos, hle => by
      simp [fdPrev]
  | fuel + 1, n + 2, hpos, hle => by
      have hmpos : 0 < (n + 2) / 2 := by omega
      have hmle : (n + 2) / 2 ≤ fuel := by omega
      have ih := fdPrev_spec fuel ((n + 2) / 2) hmpos hmle
      rw [fdPrev, ih]
      dsimp only
      set m := (n + 2) / 2 with hm
      have heven := fib_even_prev m hmpos
      have hodd := fib_odd_prev m hmpos
      by_cases hpar : (n + 2) % 2 = 0
      · rw [if_pos hpar]
        have heq : 2 * m = n + 2 := by omega
        have hpred : 2 * m - 1 = n + 1 := by omega
        rw [heq] at heven
        rw [hpred] at hodd
        have hsub : n + 2 - 1 = n + 1 := by omega
        rw [hsub, heven, hodd]
        rfl
      · rw [if_neg hpar]
        have hevenIndex : 2 * m = n + 1 := by omega
        have hoddIndex : 2 * m - 1 = n := by omega
        rw [hevenIndex] at heven
        rw [hoddIndex] at hodd
        have hnext : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) :=
          Nat.fib_add_two
        have hsub : n + 2 - 1 = n + 1 := by omega
        rw [hsub, hnext, hodd, heven, Prod.mk.injEq]
        exact ⟨Nat.add_comm _ _, rfl⟩

/--
Challenge implementation.

The `n = 0` case is separated because the worker stores F(n-1).
-/
def impl (n : Nat) : Nat :=
  if n = 0 then
    0
  else
    (fdPrev n n).1

theorem impl_correct : ∀ n, impl n = Nat.fib n := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [impl]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have h := fdPrev_spec n n hpos (Nat.le_refl n)
    rw [impl, if_neg hn, h]

end Submission
