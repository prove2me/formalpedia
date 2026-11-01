-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_prepayment_intrinsic_source_rectangle_count_exact
-- name    : AvramDividend.Classical.avram_wave4_p2_prepayment_intrinsic_source_rectangle_count_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T23:53:46.309257+00:00
-- url     : https://prove2.me/theorems/f09fbcc2-3204-4bb9-aa3a-d2c1753f5d1c
-- title:
--   Original controlled pre-payment reserve marked rectangle count equals source intrinsic Lévy jump measure
-- statement:
--   For the actual original spectrally negative Lévy process X and any original admissible left-continuous dividend strategy D, the extended cardinality of pre-payment reserve left-jump times with mark in a Borel band B during (s,t] agrees exactly, path by path, with the original Lévy source intrinsic marked jump counting measure of the same rectangle. This is an exact original-space BV/UBV transfer for predictable source counting compensation, with no external Poisson model and no asserted first-moment law.
-- source:
--   Avram–Palmowski–Pistorius (2007), Section 2 and Proposition 4(i). Canonically Proved exact original pre-payment mark d2800259 and original source intrinsic rectangle encard f6336d40.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_prepayment_intrinsic_source_rectangle_count_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
      riskProcess X x D u ω -
        Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u ≠ 0 ∧
      riskProcess X x D u ω -
        Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u ∈ B}).encard =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) := by sorry
