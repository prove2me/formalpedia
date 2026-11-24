-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_pairwise
-- name    : Formalism.CohomologicalDescent.LR.lrf_pairwise
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:42.588268+00:00
-- url     : https://prove2.me/theorems/45b8e2a0-d096-477e-a6e2-c663254b8964
-- title:
--   LR: lrf pairwise
-- statement:
--   The LR construction uses the lrf pairwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L274-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L274-L302

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

theorem Formalism.CohomologicalDescent.LR.lrf_pairwise :
    (lrf_L r n).Pairwise fun l l' => l.2.2 ≠ l'.2.2 ∧ l.2.1 ≠ l'.1 := by sorry
