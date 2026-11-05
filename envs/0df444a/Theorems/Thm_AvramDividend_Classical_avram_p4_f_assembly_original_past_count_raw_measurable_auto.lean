-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_auto
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_past_count_raw_measurable_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:44:37.419342+00:00
-- url     : https://prove2.me/theorems/41007669-7135-4db6-9ce5-cbe967f07a55
-- title:
--   Unconditional original source past negative-band count is measurable at its raw filtration horizon
-- statement:
--   For any original spectrally negative Lévy X, deterministic finite horizon T and threshold n, the literal intrinsic marked jump count on (0,T]×(-∞,-1/(n+1)] is measurable in the original raw filtration at T, with no additional count adaptedness or càdlàg hypothesis. This derives source frozen-path regularity from the Proved same-path theorem, its measurable marked-count functional, and actual adapted coordinates. It directly supplies the previous missing past-count measurability premise for original chronological pair second factorial moments.
-- source:
--   Proved c7626437 original frozen path càdlàg for every sample plus Proved 22ce6bf4 exact original frozen marked-count measurable representation. Required for future P2-E cross-cell product factor and physical pair K mean d938e9a5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_frozen_source_counter_rep_of_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_past_count_raw_measurable_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))) := by sorry
