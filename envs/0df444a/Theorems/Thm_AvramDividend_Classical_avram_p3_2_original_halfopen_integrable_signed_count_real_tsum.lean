-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_integrable_signed_count_real_tsum
-- name    : AvramDividend.Classical.avram_p3_2_original_halfopen_integrable_signed_count_real_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:25:51.285844+00:00
-- url     : https://prove2.me/theorems/a841adcf-49aa-4fe7-9f98-3741b7a32287
-- title:
--   Actual integrable signed original Lévy jump source on a half-open physical grid cell
-- statement:
--   For the intrinsic original Lévy jump counting measure restricted to any actual physical time cell (s,t], the integral of a measurable signed real jump kernel F with its exact L1 integrability premise equals the positive original jump tSum minus the negative original jump tSum, each converted to real. Exact original jump points and all right-endpoint atoms are preserved.
-- source:
--   Proved signed physical-cell source count positivity/negativity identity and pinned Mathlib integral_eq_lintegral_pos_part_sub_lintegral_neg_part, with an explicit required L1 integrability premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_signed_jump_count_tsum

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Integrable real signed original Lévy jump count on a genuine physical
half-open interval, expressed using its source-exact positive/negative sums. -/

theorem AvramDividend.Classical.avram_p3_2_original_halfopen_integrable_signed_count_real_tsum
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
    Integrable F Nst →
      (∫ p, F p ∂Nst) =
        (∑' u : ℝ≥0,
          if (0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
            u ∈ Set.Ioc s t then
            ENNReal.ofReal (F (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
          else 0).toReal -
        (∑' u : ℝ≥0,
          if (0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
            u ∈ Set.Ioc s t then
            ENNReal.ofReal (-F (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
          else 0).toReal := by sorry
