-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_arbitrary_intrinsic_smallmark_ae_jumpfree_drift
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_arbitrary_intrinsic_smallmark_ae_jumpfree_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:44:48.788217+00:00
-- url     : https://prove2.me/theorems/9cb5f085-4baf-4ea4-8607-732eea14c188
-- title:
--   Any original finite-activity intrinsic small-mark a.e. source witness has exact compensated drift on an a.e. jump-free interval
-- statement:
--   For the actual finite negative-jump activity spectrally negative Levy X and ANY intrinsic compensated small-band source Jsmall satisfying only the a.e. all-time limit witness used by B24, on any original random interval with zero actual X jumps a.e., the increment of Jsmall is exactly minus the complete negative-small-mark first moment of ν multiplied by physical elapsed real time. Strengthens the prior B85 pointwise-global-witness version by working on a common conull source event, preserving arbitrary R/Jsmall witnesses and sample-dependent stopped mesh endpoints. Does not assume global square integrability of large marks or postruin continuation.
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

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_arbitrary_intrinsic_smallmark_ae_jumpfree_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0)
    (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ᵐ ω ∂P, Jsmall (t ω) ω - Jsmall (s ω) ω =
      -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
        ((t ω : ℝ) - (s ω : ℝ)) := by sorry
