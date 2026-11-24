-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_res_mem
-- name    : Formalism.CohomologicalDescent.LR.res_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:50:38.390054+00:00
-- url     : https://prove2.me/theorems/7d937322-4776-4293-89df-7de48ea4bc1c
-- title:
--   LR: res mem
-- statement:
--   The LR construction uses the res mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L256-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L256-L271

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

theorem Formalism.CohomologicalDescent.LR.res_mem (w : ℕ) (lam2 : Fin q → ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R)
    (hf : f ∈ dualWeyl R (p + q) (p + q) (LD.blockWt p q w lam2)) : res R p q f ∈ dualWeyl R q q lam2 := by sorry
