-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_prod_upper
-- name    : Formalism.CohomologicalDescent.LR.lrf_prod_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:28.578528+00:00
-- url     : https://prove2.me/theorems/0fbe4115-6f57-4142-bde1-c2f60f2a7c23
-- title:
--   LR: lrf prod upper
-- statement:
--   The LR construction uses the lrf prod upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L445-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L445-L456

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

theorem Formalism.CohomologicalDescent.LR.lrf_prod_upper (m : Fin r × Fin n →₀ ℕ) (hm : ¬ LowerTri m) :
    (m.prod fun v k => lrf_ell R r n v ^ k) = 0 := by sorry
