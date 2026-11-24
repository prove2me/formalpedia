-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_coeffT_C_monomial_mul
-- name    : Formalism.CohomologicalDescent.LR.lrfc_coeffT_C_monomial_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:59.24912+00:00
-- url     : https://prove2.me/theorems/8e7799f6-2d0a-4966-8e7d-f895af4a53f0
-- title:
--   LR: lrfc coeff T C monomial mul
-- statement:
--   The LR construction uses the lrfc coeff T C monomial mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L61-L69

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

theorem Formalism.CohomologicalDescent.LR.lrfc_coeffT_C_monomial_mul (d s : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_coeffT d (C (monomial s 1) * G) = if s ≤ d then lrfc_coeffT (d - s) G else 0 := by sorry
