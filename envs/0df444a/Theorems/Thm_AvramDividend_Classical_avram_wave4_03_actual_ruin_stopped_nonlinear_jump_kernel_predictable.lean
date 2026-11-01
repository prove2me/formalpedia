-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_ruin_stopped_nonlinear_jump_kernel_predictable
-- name    : AvramDividend.Classical.avram_wave4_03_actual_ruin_stopped_nonlinear_jump_kernel_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:40:34.151185+00:00
-- url     : https://prove2.me/theorems/94445b12-e9b4-40d9-b089-50b180e77844
-- title:
--   Actual ruin-stopped nonlinear original Levy source-jump kernel is predictable with inclusive killing
-- statement:
--   The exact original controlled dividend reserve's nonlinear marked source-jump kernel, stopped at the actual endogenous ruinTime X x D with the crucial inclusive event s<=ruin, is predictable in the same original right-continuous filtration. It retains the ruin-causing source jump while dividends at ruin are excluded by a separate paymentTimes convention. It requires only adapted left-continuous D and measurable w, and specialises the canonical abstract stopped kernel using the authentically proved original ruin stopping-time bridge. Does not assume PRM compensation or derive an expectation identity.
-- source:
--   Original same-path stopped marked kernel af8a1cbf-30a3-4fae-be97-d7a77cae7d20, and actual ruinTime rightCont stopping time published as avram_wave4_03_actual_ruinTime_rightCont_stopping_time, from canonical original strict-event measurability db6ca856.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_controlled_stopped_prejump_marked_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_ruinTime_rightCont_stopping_time

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_actual_ruin_stopped_nonlinear_jump_kernel_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable[(𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
        (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1
          + p.2) -
         w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))) := by sorry
