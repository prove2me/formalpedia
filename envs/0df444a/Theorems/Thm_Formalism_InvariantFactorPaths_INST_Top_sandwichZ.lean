-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_Top_sandwichZ
-- name    : Formalism.InvariantFactorPaths.INST.Top.sandwichZ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:15:56.864896+00:00
-- url     : https://prove2.me/theorems/ddb28d02-e06e-4874-ae25-2ac4d6bc8344
-- title:
--   Top: sandwich Z
-- statement:
--   The Top construction uses the sandwich Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/FinalW.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/FinalW.lean#L46-L48

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

theorem Formalism.InvariantFactorPaths.INST.Top.sandwichZ : SandwichZ := by sorry
