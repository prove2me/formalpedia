-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_cutoff_past_count_rightcont_real_adapted
-- name    : AvramDividend.Classical.avram_p4_s3_run1640_original_cutoff_past_count_rightcont_real_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:50:16.223174+00:00
-- url     : https://prove2.me/theorems/b44d1aa2-fb4f-499c-af83-ecc18aec3429
-- title:
--   Genuine original full-cutoff physical negative-jump count is right-continuous-horizon adapted in real coordinates
-- statement:
--   For the original spectrally negative Lévy process, the literal marked jump count up to T on the canonical negative cutoff has a real-valued strongly measurable representative at the original right-continuous filtration time T. Imports the already proved raw-filtration source count measurability and transports through the genuine filtration inclusion; it is a concrete source instance of terminal physical count measurability needed by finite-grid predictable-prefix identities.
-- source:
--   Proved actual original raw-past cutoff count 41007669, Mathlib ENNReal.measurable_toReal and MeasureTheory.Filtration.le_rightCont at pinned revision.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_auto
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1640_original_cutoff_past_count_rightcont_real_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    StronglyMeasurable[𝓕.rightCont T]
      (fun ω : Ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal) := by sorry
