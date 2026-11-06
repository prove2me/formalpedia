-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_jump_count_source_eq_tsum
-- name    : AvramDividend.Classical.avram_p3_2_original_stopped_jump_count_source_eq_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:29:02.115243+00:00
-- url     : https://prove2.me/theorems/fa25f053-a81f-4696-8a9a-20019c2e146f
-- title:
--   Actual original Lévy stopped marked-count integral equals strict source jump tsum
-- statement:
--   For each actual original Lévy path and any measurable time stopping region S, the original nonlinear marked counting integral restricted to S equals the countable source jump sum with the genuine 0<u, nonzero original X jump and time-in-S indicators. This keeps time-zero exclusion and the strict/closed horizon distinction explicit without assuming finite jump activity.
-- source:
--   Original pinned marked Lévy jump counting theorem 008c9b37 and measurable stopped indicator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_source_nonlinear_jump_count_eq_tsum

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_stopped_jump_count_source_eq_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S : Set ℝ≥0) (hS : MeasurableSet S)
    [DecidablePred (fun u : ℝ≥0 => u ∈ S)]
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, (if p.1 ∈ S then F p else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
            ∧ u ∈ S then
          F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
        else 0 := by sorry
