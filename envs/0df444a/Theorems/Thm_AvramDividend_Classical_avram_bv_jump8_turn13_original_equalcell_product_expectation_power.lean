-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn13_original_equalcell_product_expectation_power
-- name    : AvramDividend.Classical.avram_bv_jump8_turn13_original_equalcell_product_expectation_power
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:38:51.503195+00:00
-- url     : https://prove2.me/theorems/a657c8d2-c004-4cd0-9591-191c8a08fb10
-- title:
--   Original independent stationary equal time-cell marked products have power expectation
-- statement:
--   For the actual spectrally negative Levy process, disjoint original strict-negative marked cell products are independent by its original increment independence and share the first cell law by stationary increments. Their product's expectation is the corresponding one-cell mean to the (n+1)th power.
-- source:
--   Hard stochastic child: derive independence and identical distribution of actual negative-jump cell product functionals from original Levy stationary independent increments, preserving strict endpoints. Use proved finite short-cell L1 and bounded product lemmas, then factorize the finite product expectation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn13_original_equalcell_product_expectation_power
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let J : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
      ∏ u ∈ (J ω).filter (fun u =>
        (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    (∫ ω : Ω, ∏ i : Fin (n + 1), C i ω ∂P) =
      (∫ ω : Ω, ∏ u ∈ S ω,
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) ^ (n + 1) := by sorry
