-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
-- name    : AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:41:30.950116+00:00
-- url     : https://prove2.me/theorems/282556df-2961-4f72-8851-597419378c07
-- title:
--   Full original postpayment reserve jump measure carries source Lévy marks minus simultaneous dividend right atoms
-- statement:
--   For every genuine original spectrally negative Lévy process X, admissible dividend strategy D and original sample ω, the complete nonzero positive-time marked counting measure of the postpayment reserve U⁺ equals the count restricted to times where the actual source mark ΔX minus the simultaneous right dividend-payment atom δD is nonzero, mapped to time and that exact combined mark. Equality is of Borel measures on NNReal × Real, allowing any measurable jump kernel and simultaneous source/payment atoms, with no compensator or stochastic independence assumed.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i) and equation (5.12), chronological original source-left jump followed by right dividend atom. Canonically Proved exact original postpayment mark UUID 74dd09be, original same-X jump-mark joint measurability UUID 9d68c5c2 and right-payment countable support UUID 9044d9ad; pinned Mathlib Measurable.measurable_of_countable_ne and Measure.map_apply.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightJump_support_countable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_exact_jumpmark

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
        ((x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        (x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u))) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
        ((X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
          (rightLimit D u ω - D u ω)) ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
          (rightLimit D u ω - D u ω)))) := by sorry
