-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_mem_vars
-- name    : Formalism.CohomologicalDescent.LR.lrf_mem_vars
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:42.644042+00:00
-- url     : https://prove2.me/theorems/af8e1b90-ac0c-451e-9002-978affd2b12d
-- title:
--   LR: lrf mem vars
-- statement:
--   The LR construction uses the lrf mem vars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L261-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L261-L272

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

theorem Formalism.CohomologicalDescent.LR.lrf_mem_vars (v : Fin r × Fin n) :
    v ∈ (lrf_L r n).map (·.2.2) ↔ v.2.val < v.1.val := by sorry
