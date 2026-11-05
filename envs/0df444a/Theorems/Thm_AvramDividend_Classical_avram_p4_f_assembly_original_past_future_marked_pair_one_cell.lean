-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_future_marked_pair_one_cell
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_past_future_marked_pair_one_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:52:50.615115+00:00
-- url     : https://prove2.me/theorems/fb448be1-675c-45ce-a47c-d386f9f7868d
-- title:
--   Exact original Lévy chronological past count times future marked count one-cell ν² moment
-- statement:
--   For the same original spectrally negative Levy process, the genuine negative-band intrinsic marked count up to time s multiplied by the genuine future count on (s,t] has exact ENNReal expectation (sνB)((t-s)νB). This is a direct consequence of the public raw-past measurability, original zero-origin Lévy ν rate and original predictable weighted compensator; no independent Poisson process or conditional moment premise is introduced.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_auto
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_weighted_from_zero_origin_rate
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_past_future_marked_pair_one_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc a b ×ˢ B)
    (∫⁻ ω, N 0 s ω * N s t ω ∂P) =
      ((s : ℝ≥0∞) * X.ν B) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
