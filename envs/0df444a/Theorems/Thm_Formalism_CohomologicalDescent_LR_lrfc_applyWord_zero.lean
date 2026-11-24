-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_applyWord_zero
-- name    : Formalism.CohomologicalDescent.LR.lrfc_applyWord_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:08.237138+00:00
-- url     : https://prove2.me/theorems/3b66fcb4-1647-4408-93b9-622e7b8b3809
-- title:
--   LR: lrfc apply Word zero
-- statement:
--   The LR construction uses the lrfc apply Word zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L131-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L131-L138

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

theorem Formalism.CohomologicalDescent.LR.lrfc_applyWord_zero (w : List (Fin r × Fin r × ℕ)) :
    applyWord R w (0 : MvPolynomial (Fin r × Fin n) R) = 0 := by sorry
