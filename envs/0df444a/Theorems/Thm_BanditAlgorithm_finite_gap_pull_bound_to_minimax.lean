-- Prove2me | Theorems.Thm_BanditAlgorithm_finite_gap_pull_bound_to_minimax
-- name    : BanditAlgorithm.finite_gap_pull_bound_to_minimax
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T22:27:04.350056+00:00
-- url     : https://prove2.me/theorems/b8fb0ac0-129e-4d6c-ba5e-cee7cd81a51d
-- title:
--   From gap-dependent pull bounds to minimax regret
-- statement:
--   Let $k\ge1$ and $n\ge2$. For each arm $i$, let its gap satisfy $0\le\Delta_i\le1$, and let $T_i\ge0$ be an expected pull count with $\sum_iT_i=n$. Suppose that every positive-gap arm satisfies the logarithmic instance-dependent estimate
--
--   $$
--   T_i\le C\left(1+\frac{\log n}{\Delta_i^2}\right),
--   \qquad C\ge0.
--   $$
--
--   Then the corresponding regret obeys the distribution-free bound
--
--   $$
--   \sum_i\Delta_iT_i
--   \le(1+3C)\sqrt{kn\log n}.
--   $$
--
--   This is the standard small-gap/large-gap conversion: split at $\sqrt{k\log(n)/n}$, control small gaps using the total pull count, and control large gaps using the instance-dependent estimate.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Theorem 36.3, printed p.465, distribution-free conclusion; standard small-gap/large-gap conversion used throughout Chapters 7-9.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

theorem BanditAlgorithm.finite_gap_pull_bound_to_minimax {k n : ℕ} [NeZero k]
    (hn : 2 ≤ n) (Δ T : Fin k → ℝ) (C : ℝ)
    (hΔ : ∀ i, Δ i ∈ Set.Icc (0 : ℝ) 1)
    (hT : ∀ i, 0 ≤ T i) (hsum : ∑ i, T i = n)
    (hC : 0 ≤ C)
    (hpull : ∀ i, 0 < Δ i →
      T i ≤ C * (1 + Real.log n / Δ i ^ 2)) :
    ∑ i, Δ i * T i ≤
      (1 + 3 * C) * Real.sqrt (k * n * Real.log n) := by
  sorry
