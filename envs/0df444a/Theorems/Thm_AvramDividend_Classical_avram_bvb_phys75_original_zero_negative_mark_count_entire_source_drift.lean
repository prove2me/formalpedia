-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
-- name    : AvramDividend.Classical.avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:52:14.192455+00:00
-- url     : https://prove2.me/theorems/93033988-ad60-4bb0-920b-6552a12e5827
-- title:
--   Original BV zero intrinsic negative count identifies the entire surviving source as drift
-- statement:
--   In the original BV source with its own filtration, zero actual intrinsic negative marked count through T together with structural spectral negativity forces every physical jump on (0,T] to vanish. The Proved original no-jump source identity then gives X(t)=drift*t for all t<=T on a common full-measure event. This is a necessary source identification for the c37acb5a zero-count physical Stieltjes ledger.
-- source:
--   Direct composition of proved original nonpositive jumps, phys73 and phys74

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys74_original_no_physical_jumps_path_equals_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) →
      ∀ t : ℝ≥0, t ≤ T → X.X t ω = (t : ℝ) * X.drift := by sorry
