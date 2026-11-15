-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_smallmark_all_jumpfree_cells_common_conull_drift
-- name    : AvramDividend.Classical.avram_b24_original_smallmark_all_jumpfree_cells_common_conull_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:51:07.528442+00:00
-- url     : https://prove2.me/theorems/a06fac51-ec1d-465a-8b0c-2304497dd042
-- title:
--   Original small-mark compensated source exact drift on all jump-free physical grid cells simultaneously a.e.
-- statement:
--   For every original same-space finite-activity intrinsic compensated mark witness Jsmall satisfying an a.e. all-time residual limit, on one common conull event, its increment equals the complete negative smallmark compensation drift times elapsed time on EVERY jumpfree original interval [s,t]. There is no stronger globally pointwise convergence hypothesis and no need to select finitely many mesh times in advance. This directly supports physical random-grid interior cells and separates true negative marked ruin contact jumps from jumpfree compensated drift.
-- source:
--   Proved B80 exact finite cutoff on physical jumpfree cell and B84 finite-activity negative small-mark moment convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_smallmark_all_jumpfree_cells_common_conull_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω))) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (∀ u : ℝ≥0, s < u → u ≤ t →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      Jsmall t ω - Jsmall s ω =
        -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) * ((t : ℝ) - (s : ℝ)) := by sorry
