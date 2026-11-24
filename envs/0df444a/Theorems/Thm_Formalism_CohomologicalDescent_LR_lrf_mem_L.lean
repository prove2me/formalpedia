-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_mem_L
-- name    : Formalism.CohomologicalDescent.LR.lrf_mem_L
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:54.883877+00:00
-- url     : https://prove2.me/theorems/89b78797-7ec1-41af-a4da-7961399e74bf
-- title:
--   LR: lrf mem L
-- statement:
--   The LR construction uses the lrf mem L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L246-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L246-L259

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

theorem Formalism.CohomologicalDescent.LR.lrf_mem_L (l : Fin r × Fin r × (Fin r × Fin n)) :
    l ∈ lrf_L r n ↔ l.1.val = l.2.2.2.val ∧ l.2.2.2.val < l.2.1.val ∧ l.2.2.1 = l.2.1 := by sorry
