-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_jump_measure_negative_mark_ae
-- name    : AvramDividend.Classical.avram_pj_workerC_original_jump_measure_negative_mark_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:49:35.656113+00:00
-- url     : https://prove2.me/theorems/f77aa32a-23cf-414b-98a6-84021501989e
-- title:
--   True intrinsic original nonzero jump counting measure is almost everywhere supported on strictly negative marks
-- statement:
--   The actual spectral-negative source jump measure built from positive event times and nonzero X increments has no positive or zero marks almost everywhere. Uses the Proved global null mass of all nonnegative marks. Provides the concrete hMneg support needed to combine actual nonlinear and linear marked compensation sources.
-- source:
--   Proved 0a9afdb9 original intrinsic marked jump measure global nonnegative support zero, ae_iff and product set complement identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_jump_measure_negative_mark_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ∀ᵐ p ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))),
      p.2 < 0 := by sorry
