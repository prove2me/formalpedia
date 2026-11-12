-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
-- name    : AvramDividend.Classical.avram_ja34_original_all_negative_borel_expected_count_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:25:29.033613+00:00
-- url     : https://prove2.me/theorems/0d444e07-74c9-4850-b1f8-7fa08335b493
-- title:
--   Every original negative Borel mark has exact first raw count moment T ν(B)
-- statement:
--   For the actual original spectrally negative Lévy process and any measurable negative Borel mark set, the expectation of the physical marked count in a finite time horizon is precisely time multiplied by Lévy measure intensity. Derive by identifying zero-origin rates on separated Borel sets and the already Proved measure-uniqueness extension to all negative Borel sets.
-- source:
--   Proved avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate 34dbea70 and avram_p2_c_borel_original_intrinsic_rate_restricted_nu_of_unit_separated_bands 50e8e462.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja34_original_all_negative_borel_expected_count_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) =
      (T : ℝ≥0∞) * X.ν B := by sorry
