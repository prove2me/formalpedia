-- Prove2me | Theorems.Thm_DiscrNeWork_discrNe_all
-- name    : DiscrNeWork.discrNe_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:44.13666+00:00
-- url     : https://prove2.me/theorems/7b16e2e8-4ad2-45c7-a13f-a13a456e883b
-- title:
--   Discr Ne Work: discr Ne all
-- statement:
--   The Discr Ne Work construction uses the discr Ne all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscMain.lean#L140-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NonzeroDiscriminants/DiscMain.lean#L140-L153

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

theorem DiscrNeWork.discrNe_all : PI.DiscrNe := by sorry
