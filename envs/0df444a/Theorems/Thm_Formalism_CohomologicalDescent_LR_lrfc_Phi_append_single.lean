-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_Phi_append_single
-- name    : Formalism.CohomologicalDescent.LR.lrfc_Phi_append_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:05.366801+00:00
-- url     : https://prove2.me/theorems/4394fe49-c1bd-4897-8bbf-24bac31c7dcb
-- title:
--   LR: lrfc Phi append single
-- statement:
--   The LR construction uses the lrfc Phi append single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L118-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L118-L124

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

theorem Formalism.CohomologicalDescent.LR.lrfc_Phi_append_single (w : List (Fin r × Fin r × (Fin r × Fin n)))
    (l : Fin r × Fin r × (Fin r × Fin n))
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_Phi (w ++ [l]) G = lrfc_Phi w (lrfc_tau l G) := by sorry
