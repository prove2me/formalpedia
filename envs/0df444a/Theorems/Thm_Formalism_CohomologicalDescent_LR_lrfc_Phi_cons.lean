-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_Phi_cons
-- name    : Formalism.CohomologicalDescent.LR.lrfc_Phi_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:16.767073+00:00
-- url     : https://prove2.me/theorems/626234e8-0a59-4b2a-92f3-56469030d8b3
-- title:
--   LR: lrfc Phi cons
-- statement:
--   The LR construction uses the lrfc Phi cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L114-L116

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

theorem Formalism.CohomologicalDescent.LR.lrfc_Phi_cons (l : Fin r × Fin r × (Fin r × Fin n)) (w : List (Fin r × Fin r × (Fin r × Fin n)))
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_Phi (l :: w) G = lrfc_tau l (lrfc_Phi w G) := by sorry
