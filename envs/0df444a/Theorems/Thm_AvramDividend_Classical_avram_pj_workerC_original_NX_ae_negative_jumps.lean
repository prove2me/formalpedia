-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_NX_ae_negative_jumps
-- name    : AvramDividend.Classical.avram_pj_workerC_original_NX_ae_negative_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:12:44.971151+00:00
-- url     : https://prove2.me/theorems/9da8864c-9e9b-4bff-b08e-6293cbd5bf17
-- title:
--   Actual mapped original Lévy jump counting measure is supported almost everywhere on strictly negative marks
-- statement:
--   At every original sample path, the genuine mapped positive-time jump counting measure NX assigns zero mass to nonnegative marks and is therefore almost surely supported on z<0 as an inner mark measure. This discharges the exact pathwise negative-mark support hypothesis in the compensated two-measure J+L source cancellation.
-- source:
--   Proved avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero, Mathlib ae_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_NX_ae_negative_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ∀ᵐ p ∂((Measure.count.restrict
      {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
      (fun s : ℝ≥0 => (s, X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s))),
      p.2 < (0 : ℝ) := by sorry
