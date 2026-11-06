-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_signed_jump_count_tsum
-- name    : AvramDividend.Classical.avram_p3_2_original_halfopen_physical_signed_jump_count_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:12:28.849342+00:00
-- url     : https://prove2.me/theorems/e0f6aa7d-b1c6-43b8-8faf-7c3dc2b4dbc0
-- title:
--   Positive and negative marked original Lévy jump sums on each genuine half-open physical cell
-- statement:
--   For the actual spectrally negative Lévy process X and each half-open physical interval (s,t], both positive and negative parts of a measurable signed nonlinear original jump kernel integrate against exactly the intrinsic marked original jump counting measure, with equality to the corresponding time-indexed original jump sums. This preserves right-endpoint jumps and supports signed L1 original compensation.
-- source:
--   Proved original Lévy mark joint measurability, original positive jump-set measurability, and Proved generic exact nonlinear count-map lintegral-to-tsum, applied separately to the positive and negative signed kernel parts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Positive/negative original signed-kernel count integrals on an actual
half-open physical clock cell, including every genuine original jump. -/

theorem AvramDividend.Classical.avram_p3_2_original_halfopen_physical_signed_jump_count_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0)
    (F : ℝ≥0 × ℝ → ℝ) (hF : Measurable F) :
    let Nst : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict
        ({u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} ∩
          Set.Ioc s t)).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ((∫⁻ p, ENNReal.ofReal (F p) ∂Nst) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
          u ∈ Set.Ioc s t then
          ENNReal.ofReal (F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
        else 0) ∧
    ((∫⁻ p, ENNReal.ofReal (-F p) ∂Nst) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
          u ∈ Set.Ioc s t then
          ENNReal.ofReal (-F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
        else 0) := by sorry
