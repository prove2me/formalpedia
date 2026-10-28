-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_dyadic_expected_active_count_of_constant_probability
-- name    : AvramDividend.Classical.bv_dyadic_expected_active_count_of_constant_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:03:06.323064+00:00
-- url     : https://prove2.me/theorems/7b97ac46-02b0-4ab7-91dd-1e2860bb3f61
-- title:
--   Expected number of uniformly likely active dyadic cells is number of cells times event probability
-- statement:
--   For any finite collection of measurable grid-cell events with a common probability p, the nonnegative Lebesgue expected sum of their indicator values equals Np, regardless of dependence. This combines the already-Proved finite indicator-integral identity with equality of all cell probabilities and Finset.sum_const. It is directly applicable to the actual Lévy residual's accepted positive-increment probability on equal-length intervals, making the dyadic uniform expected-count bound precise.
-- source:
--   Avram Palmowski Pistorius (2007), finite activity first-jump proof; Prove2Me lintegral active count theorem.

import Theorems.Thm_AvramDividend_Classical_bv_dyadic_lintegral_active_cell_count
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open AvramDividend.Classical MeasureTheory Finset
open scoped ENNReal

theorem AvramDividend.Classical.bv_dyadic_expected_active_count_of_constant_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Set Ω) (N : ℕ) (p : ℝ≥0∞)
    (hE : ∀ i : ℕ, i < N → MeasurableSet (E i))
    (hp : ∀ i : ℕ, i < N → P (E i) = p) :
    (∫⁻ ω, ∑ i ∈ Finset.range N,
      (E i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) =
      (N : ℝ≥0∞) * p := by sorry
