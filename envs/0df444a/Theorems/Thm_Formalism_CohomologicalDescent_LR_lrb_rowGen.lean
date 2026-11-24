-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_rowGen
-- name    : Formalism.CohomologicalDescent.LR.lrb_rowGen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:51:03.195778+00:00
-- url     : https://prove2.me/theorems/3418f4b3-d798-4329-9343-14355d3dcb2a
-- title:
--   LR: lrb row Gen
-- statement:
--   The LR construction uses the lrb row Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L63-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L63-L87

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

theorem Formalism.CohomologicalDescent.LR.lrb_rowGen (b b' : Fin q) :
    (Polynomial.mapAlgHom (res R p q)).comp (rowGen R (Fin.natAdd p b) (Fin.natAdd p b')) =
      (rowGen R b b').comp (res R p q) := by sorry
