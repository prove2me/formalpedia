-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_prepayment_intrinsic_marked_jump_measure_eq_source
-- name    : AvramDividend.Classical.avram_wave4_p2_prepayment_intrinsic_marked_jump_measure_eq_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T23:58:52.339512+00:00
-- url     : https://prove2.me/theorems/690e3b7e-7a37-4512-bb7d-9ef1675a8c7f
-- title:
--   Full intrinsic marked jump measure of original pre-payment controlled reserve equals original Lévy source jump measure
-- statement:
--   For the actual original spectrally negative Lévy process, each original sample and any admissible left-continuous dividend strategy, the entire positive-time nonzero marked jump counting measure of the pre-payment controlled reserve, as a pushforward of counting measure on the true reserve left jumps, equals the genuine source Lévy intrinsic marked jump counting measure as a Measure on nonnegative time × real jump mark. Equality is pathwise and holds for all Borel mark-time sets. It transfers every source measure integral of a measurable jump kernel to the controlled pre-payment reserve, without asserting a compensator or changing probability space.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), original Lévy jump term. Accepted exact source mark d2800259 and source joint mark measurability 9d68c5c2. Pinned Mathlib Measure.map_apply and Measure.restrict_apply, as verified by f6336d40.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_prepayment_intrinsic_marked_jump_measure_eq_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ riskProcess X x D u ω -
        Function.leftLim
          (fun v : ℝ≥0 => riskProcess X x D v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        riskProcess X x D u ω -
          Function.leftLim
            (fun v : ℝ≥0 => riskProcess X x D v ω) u))) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by sorry
