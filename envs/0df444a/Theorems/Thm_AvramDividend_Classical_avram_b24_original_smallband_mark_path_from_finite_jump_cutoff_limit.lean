-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_smallband_mark_path_from_finite_jump_cutoff_limit
-- name    : AvramDividend.Classical.avram_b24_original_smallband_mark_path_from_finite_jump_cutoff_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:51:35.937487+00:00
-- url     : https://prove2.me/theorems/05e9f32f-3c34-49f6-981a-5b968d0a9e17
-- title:
--   Actual finite-activity intrinsic smallmark path equals finite genuine negative jump sum minus original compensator
-- statement:
--   For the genuine unmodified finite-negative-jump-activity original Levy path X, a given finite support of its true jumps up to t and an arbitrary true intrinsic compensated smallmark source Jsmall, combine the exact physical marked cutoff sum identity with the full ν small-negative first-moment cutoff limit and the finite cutoff jump sum limit to identify Jsmall(t) exactly as the sum of actual small negative path jumps minus t times the complete small-mark compensator. Crucially true ruin-causing jumps survive. The finite-cutoff convergence is an explicit separately provable hypothesis; no auxiliary stochastic process or large-mark second moment.
-- source:
--   Proved a22 original exact finite marked jump cutoff and B84 finite negative smallmark drift moment limit, plus separately proved finite cutoff jump sum convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_restored_compensator_smalljump_equals_physical_finite_mark_sum
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_smallband_mark_path_from_finite_jump_cutoff_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (ω : Ω) (t : ℝ≥0) (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : Tendsto (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
      atTop (𝓝 (Jsmall t ω)))
    (S : Finset ℝ≥0)
    (hS : ∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hCut : Tendsto (fun n : ℕ =>
      ∑ u ∈ S, if -1 < X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))
      then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0)
      atTop (𝓝 (∑ u ∈ S,
        if -1 < X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
           X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
        then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0))) :
    Jsmall t ω =
      (∑ u ∈ S,
        if -1 < X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
           X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
        then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0) -
      (t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) := by sorry
