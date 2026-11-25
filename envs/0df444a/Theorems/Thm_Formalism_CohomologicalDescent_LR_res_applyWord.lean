-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_res_applyWord
-- name    : Formalism.CohomologicalDescent.LR.res_applyWord
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:23:54.995638+00:00
-- url     : https://prove2.me/theorems/9146b715-debc-4b8c-80b7-535f30928fef
-- title:
--   LR: res apply Word
-- statement:
--   The LR construction uses the res apply Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L95-L101

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

theorem Formalism.CohomologicalDescent.LR.res_applyWord (ω : List (Fin q × Fin q × ℕ)) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R) :
    res R p q (applyWord R (liftWord p ω) f) = applyWord R ω (res R p q f) := by sorry
