-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_eval_Phi
-- name    : Formalism.CohomologicalDescent.LR.lrf_eval_Phi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:55.50538+00:00
-- url     : https://prove2.me/theorems/74662b59-6323-44ad-910d-15e472a41959
-- title:
--   LR: lrf eval Phi
-- statement:
--   The LR construction uses the lrf eval Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L393-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L393-L408

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
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
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.CohomologicalDescent.LR.lrf_eval_Phi (F : MvPolynomial (Fin r × Fin n) R) :
    eval (lrf_idS R r n) (lrfc_Phi (lrf_L r n) (lrfc_iota F)) = eval₂ C (lrf_ell R r n) F := by sorry
