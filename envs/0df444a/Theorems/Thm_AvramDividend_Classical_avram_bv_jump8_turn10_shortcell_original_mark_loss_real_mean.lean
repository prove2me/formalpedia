-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_shortcell_original_mark_loss_real_mean
-- name    : AvramDividend.Classical.avram_bv_jump8_turn10_shortcell_original_mark_loss_real_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:48:53.734304+00:00
-- url     : https://prove2.me/theorems/d2bb024c-2663-4740-b31b-d7f35c044924
-- title:
--   Original-X strict negative marked loss finite sum has exact real-valued Lévy compensator mean
-- statement:
--   Upgrade the already Proved source-exact ENNReal Campbell compensator identity db9a5093 to the real Bochner integral of the finite literal original-X strict negative marked jump loss, with exact (0,T] zero-origin convention and no finite-total-activity hypothesis.
-- source:
--   Upgrade the already Proved source-exact ENNReal Campbell compensator identity db9a5093 to the real Bochner integral of the finite literal original-X strict negative marked jump loss, with exact (0,T] zero-origin convention and no finite-total-activity hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn10_shortcell_original_mark_loss_real_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    (∫ ω, L ω ∂P) =
      (1 / ((n : ℝ) + 1)) *
      (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν) := by sorry
