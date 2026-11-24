-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_coeffT_monomial
-- name    : Formalism.CohomologicalDescent.LR.lrfc_coeffT_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:50.047406+00:00
-- url     : https://prove2.me/theorems/219bd5a5-f991-424c-9a8e-c50f6f9ea6fd
-- title:
--   LR: lrfc coeff T monomial
-- statement:
--   The LR construction uses the lrfc coeff T monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L54-L59

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

theorem Formalism.CohomologicalDescent.LR.lrfc_coeffT_monomial (d u : Fin r × Fin n →₀ ℕ) (c : MvPolynomial (Fin r × Fin n) R) :
    lrfc_coeffT d (monomial u c) = monomial u (coeff d c) := by sorry
