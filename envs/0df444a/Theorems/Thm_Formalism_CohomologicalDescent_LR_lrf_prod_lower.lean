-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_prod_lower
-- name    : Formalism.CohomologicalDescent.LR.lrf_prod_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:53.037988+00:00
-- url     : https://prove2.me/theorems/a1470e0b-e0a3-48e2-b932-e608007e8e23
-- title:
--   LR: lrf prod lower
-- statement:
--   The LR construction uses the lrf prod lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L423-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L423-L443

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

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

theorem Formalism.CohomologicalDescent.LR.lrf_prod_lower (m : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) :
    (m.prod fun v k => lrf_ell R r n v ^ k) = monomial (lrf_off m) 1 := by sorry
