-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_cell_marked_nonlinear_count_tsum
-- name    : AvramDividend.Classical.avram_p3_2_original_halfopen_physical_cell_marked_nonlinear_count_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:57:17.945455+00:00
-- url     : https://prove2.me/theorems/0da10fb9-956f-49c7-b2ee-20dd63d355d7
-- title:
--   Original nonlinear Lévy marked-count integral restricted to an actual half-open physical grid cell
-- statement:
--   For every original spectrally negative Lévy sample path and each physical grid cell (s,t], the integral of a measurable nonnegative nonlinear jump kernel against the intrinsic original jump count restricted to that cell equals exactly the sum over genuine original marked jumps in that cell. Includes zero-origin and right-endpoint logic without finite-activity assumptions or an independent Poisson proxy.
-- source:
--   Pinned generic nonlinear marked-count identity, original joint jump-mark measurability, original jump-time set measurability and measurable half-open time interval; a direct source-faithful step towards identifying physical-grid nonlinear jump terms with the stopped original marked integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Genuine original spectrally negative Levy marked-count integrals on one
half-open physical grid cell, retaining every original negative jump. -/

theorem AvramDividend.Classical.avram_p3_2_original_halfopen_physical_cell_marked_nonlinear_count_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂
      ((Measure.count.restrict
        ({u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} ∩
          Set.Ioc s t)).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
            u ∈ Set.Ioc s t then
          F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
        else 0 := by sorry
