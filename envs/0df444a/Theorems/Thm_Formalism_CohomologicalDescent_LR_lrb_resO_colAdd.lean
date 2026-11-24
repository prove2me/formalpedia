-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_resO_colAdd
-- name    : Formalism.CohomologicalDescent.LR.lrb_resO_colAdd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:51:18.217322+00:00
-- url     : https://prove2.me/theorems/a8a8c136-9b71-43e6-a57d-89d7015e6fc7
-- title:
--   LR: lrb res O col Add
-- statement:
--   The LR construction uses the lrb res O col Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L232-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L232-L254

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable (R : Type*) [CommRing R] (p q : ℕ)

theorem Formalism.CohomologicalDescent.LR.lrb_resO_colAdd (l j : Fin q) :
    (lrbResO R p q).comp (colAddGen R (Fin.natAdd p l) (Fin.natAdd p j)) = (colAddGen R l j).comp (res R p q) := by sorry
