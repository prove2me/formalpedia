-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn12_real_loss_ofReal_sum
-- name    : AvramDividend.Classical.avram_bv_jump8_turn12_real_loss_ofReal_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:19:30.204235+00:00
-- url     : https://prove2.me/theorems/1906d3b2-5eb7-47a0-8b9b-e1fa88fd67a6
-- title:
--   Original negative marked finite loss has nonnegative real and ENNReal sum agreement
-- statement:
--   Every time in the finite original strict negative mark set contributes a nonnegative real loss 1-exp(ΔX), so the loss sum is nonnegative and the finite sum of ENNReal.ofReal terms is ENNReal.ofReal of the real loss sum.
-- source:
--   Finite-sum nonnegative arithmetic using the original strict negative cutoff and ENNReal.ofReal_sum_of_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn12_real_loss_ofReal_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    ∀ ω : Ω, 0 ≤ L ω ∧
      (∑ u ∈ S ω, ENNReal.ofReal
        (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
      ENNReal.ofReal (L ω) := by sorry
