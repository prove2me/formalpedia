-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_Top_unitsOfLocal
-- name    : Formalism.InvariantFactorPaths.INST.Top.unitsOfLocal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:34:57.610226+00:00
-- url     : https://prove2.me/theorems/19f458ea-d62c-423a-863d-ab10364d8867
-- title:
--   Top: units Of Local
-- statement:
--   The Top construction uses the units Of Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/FinalW.lean#L20-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/FinalW.lean#L20-L38

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_SwappedHighestWeightNeZero
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Descent
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Ascent
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Assemble
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_FinalW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST Formalism.InvariantFactorPaths.INST.Top

theorem Formalism.InvariantFactorPaths.INST.Top.unitsOfLocal : UnitsOfLocal := by sorry
