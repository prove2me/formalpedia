-- Prove2me | Theorems.Thm_DiscrNeWork_discr_ne_of_pos
-- name    : DiscrNeWork.discr_ne_of_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:51.712908+00:00
-- url     : https://prove2.me/theorems/f3cd300b-e0e5-4c47-88e2-c45efc692eff
-- title:
--   Discr Ne Work: discr ne of pos
-- statement:
--   The Discr Ne Work construction uses the discr ne of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscMain.lean#L123-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscMain.lean#L123-L138

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NonzeroDiscriminants_DiscMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ModularForm EisensteinSeries UpperHalfPlane
noncomputable section
open DiscrNeWork

theorem DiscrNeWork.discr_ne_of_pos (w₁ w₂ : ℂ) (h : 0 < ((starRingEnd ℂ) w₁ * w₂).im) :
    PI.discr (PI.lat2 w₁ w₂) ≠ 0 := by sorry
