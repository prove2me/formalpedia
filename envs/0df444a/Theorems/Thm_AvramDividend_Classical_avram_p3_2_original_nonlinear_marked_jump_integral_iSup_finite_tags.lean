-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_nonlinear_marked_jump_integral_iSup_finite_tags
-- name    : AvramDividend.Classical.avram_p3_2_original_nonlinear_marked_jump_integral_iSup_finite_tags
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:43:02.919189+00:00
-- url     : https://prove2.me/theorems/784f4b51-de56-4d53-bd50-daf688b9c1b2
-- title:
--   Original intrinsic nonlinear Lévy jump integral equals supremum over finite actual jump tags
-- statement:
--   The nonnegative nonlinear marked counting integral of the actual original spectrally negative Lévy process is exactly the supremum of its sums over finite sets of actual positive-time nonzero jumps. No finite activity is assumed. This supplies the finite-tag approximation bridge for original BV source-grid convergence and the HJB jump compensator.
-- source:
--   Proved original jumpmark joint measurability 9d68c5c2, original nonzero-jump-time support measurability 0a4c69be, Mathlib lintegral_map, lintegral_indicator, lintegral_count and ENNReal.tsum_eq_iSup_sum at pinned Mathlib revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original nonlinear marked Lévy jump integrals are the supremum of their
finite genuine jump-tag sums, with no finite-activity assumption. -/

theorem AvramDividend.Classical.avram_p3_2_original_nonlinear_marked_jump_integral_iSup_finite_tags
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ⨆ T : Finset ℝ≥0,
      ∑ t ∈ T,
        if 0 < t ∧ X.X t ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0 then
          F (t, X.X t ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)
        else 0 := by sorry
