-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_lower_survival_min_equiv
-- name    : AvramDividend.Classical.finite_grid_lower_survival_min_equiv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:48:23.147102+00:00
-- url     : https://prove2.me/theorems/f7b67b54-dc92-48f4-910c-226cbab98de3
-- title:
--   Discrete survival threshold expressed by the least observed reserve
-- statement:
--   For any nonempty finite schedule of times, reserve is nonnegative at every observed instant if and only if the initial reserve plus the minimum sampled Lévy value is nonnegative. Provides the finite-dimensional approximation used in running-infimum survival and Laplace-Tonelli arguments.
-- source:
--   Finite nonempty infimum inequalities Finset.le_inf' and Finset.inf'_le. Complements the proved continuous running-infimum survival equivalence without using the exit identity.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.finite_grid_lower_survival_min_equiv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : Finset ℕ) (hs : s.Nonempty)
    (τ : ℕ → ℝ≥0) (ω : Ω) (x : ℝ) :
    (∀ k : ℕ, k ∈ s → 0 ≤ x + X.X (τ k) ω) ↔
      0 ≤ x + s.inf' hs (fun k => X.X (τ k) ω) := by sorry
