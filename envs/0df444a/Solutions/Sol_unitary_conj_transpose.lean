-- Prove2me | solution 1 for unitary_conj_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:10:40.396738+00:00
-- url     : https://prove2.me/submissions/1094cf9a-9486-45ff-b1e9-3172f07087d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_ConjTransposeOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_ExistsUnitReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_Transfer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_SubmatrixMemUnitaryGroup
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UConjT
import Theorems.Thm_PI_UConjT_blockStep
import Theorems.Thm_PI_UConjT_conjTranspose_of
import Theorems.Thm_PI_UConjT_onbReal
import Theorems.Thm_PI_UConjT_transferStep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.UMultOne.ConjTranspose :=
  PI.UConjT.conjTranspose_of PI.UConjT.onbReal PI.UConjT.transferStep PI.UConjT.blockStep
