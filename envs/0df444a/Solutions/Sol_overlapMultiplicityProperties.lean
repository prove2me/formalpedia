-- Prove2me | solution 1 for overlapMultiplicityProperties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:55:06.966883+00:00
-- url     : https://prove2.me/submissions/f1af7fa7-485f-41d0-9583-a156225327e3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldMult
import Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_measurable_mult
import Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_mult_lt_top
import Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_mult_mul_left
import Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_one_le_mult


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.FoldMult.UnitaryGroupMassFormula
theorem _root_.solution : PI.FoldMult.FoldMult := by
  intro G _ _ _ _ _ _ _ Γ hΓ Ω hΩ h1
  exact ⟨fun x => one_le_mult Γ Ω h1 x, fun x => mult_lt_top Γ Ω hΩ x,
    fun γ hγ x => mult_mul_left Γ Ω γ hγ x, measurable_mult Γ Ω hΩ⟩
