-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_prepayment_intrinsic_positive_mark_rectangle_zero
-- name    : AvramDividend.Classical.avram_wave4_p2_prepayment_intrinsic_positive_mark_rectangle_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:14:24.873434+00:00
-- url     : https://prove2.me/theorems/689f4de0-1860-4dda-83fd-9fa1cab0b234
-- title:
--   Original controlled pre-payment intrinsic jump measure charges no positive-mark rectangle
-- statement:
--   For every original spectrally negative Lévy X and admissible left-continuous dividend strategy D, the intrinsic marked jump counting measure of the actual pre-payment reserve assigns exactly zero mass to (s,t]×(0,∞), path by path, in both bounded and unbounded variation. Original source marks are nonpositive and the pre-payment marks agree with them at every positive time. This closes the deterministic zero-positive-mark half of the original predictable marked compensator without assuming any Poisson intensity or stopped Itô theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 2 and Proposition 4(i). Canonically Proved original source mark sign e95fe5bc, original pre-payment mark d2800259 and source rectangle count f09fbcc2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_prepayment_intrinsic_source_rectangle_count_exact

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_prepayment_intrinsic_positive_mark_rectangle_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t : ℝ≥0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ riskProcess X x D u ω -
        Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        riskProcess X x D u ω -
          Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u)))
      (Ioc s t ×ˢ Ioi (0 : ℝ)) = 0 := by sorry
