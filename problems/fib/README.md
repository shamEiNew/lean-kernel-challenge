# Fibonacci — participant workspace

Edit `Submission.lean` and prove `∀ n, impl n = Nat.fib n`. See the
[problem statement](../../rules/problems/fib.md) for the specification,
examples, test groups, and scoring.

## Quick start

Install [elan](https://github.com/leanprover/elan), Git, and Python 3.9+. From
the repository root:

```bash
cd problems/fib
python3 setup.py
lake build
```

Setup prepares pinned Mathlib dependencies and initially needs network access.
Keep `Spec.lean` and the environment files unchanged; submit only
`Submission.lean`. `lake build` checks compilation and proofs, not official
acceptance or performance. For optional local evaluation, see the
[evaluator guide](../../evaluation/README.md). The starter is not guaranteed to
pass every performance case.

## Measured improvement

- **Baseline:** fast doubling, 67,175,513 leaderboard instructions.
- **Change:** replaced Fibonacci arithmetic using `+` and `*` with direct `Nat.add` and `Nat.mul` calls, reducing kernel wrapper overhead. Formulas and recursion stayed unchanged.
- **Result:** 57,459,041 instructions — **14.5% fewer**. This is our new baseline; correctness and all six local evaluation cases passed.
- **Discarded experiment:** two-square formulas increased playground instructions by 31%, so we reverted them.
