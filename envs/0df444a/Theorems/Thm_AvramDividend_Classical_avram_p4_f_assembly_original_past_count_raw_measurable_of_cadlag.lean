-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_of_cadlag
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_past_count_raw_measurable_of_cadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:41:33.622329+00:00
-- url     : https://prove2.me/theorems/0022b5d6-7dad-43f2-aa04-60da4a9e1014
-- title:
--   Original separated negative-band past count is raw-filtration measurable from source càdlàg frozen paths
-- statement:
--   For the actual original spectrally negative Lévy process and raw filtration, if its original path frozen at deterministic horizon T is càdlàg for every sample, the intrinsic marked count of original jumps in (0,T]×(-∞,-1/(n+1)] is measurable at time T. The proof reuses the accepted exact original frozen-path functional and original adaptedness. The stated path regularity is an explicit premise and is not silently inferred from an a.s. càdlàg property.
-- source:
--   Accepted original frozen-prefix marked count 22ce6bf4 and original raw filtration measurability source 735b8fa1. Required to use original P2-E past-weighted compensation with the count in an earlier dyadic cell when proving original chronological factorial moment d938e9a5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_frozen_source_counter_rep_of_cadlag
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_past_count_raw_measurable_of_cadlag
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (hCad : ∀ ω : Ω,
      (∀ u : ℝ≥0, ContinuousWithinAt
        (fun v : ℝ≥0 => X.X (min v T) ω) (Ici u) u) ∧
      (∀ u : ℝ≥0, 0 < u →
        ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => X.X (min v T) ω)
          (𝓝[<] u) (𝓝 l))) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))) := by sorry
