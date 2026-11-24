-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_pt
-- name    : Formalism.CohomologicalDescent.LR.lrf_pt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:31.641512+00:00
-- url     : https://prove2.me/theorems/0cfd0bd7-3609-4a3e-82d3-e3af477ab35b
-- title:
--   LR: lrf pt
-- statement:
--   The LR construction uses the lrf pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L327-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L327-L386

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

theorem Formalism.CohomologicalDescent.LR.lrf_pt (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (hP : L.Pairwise fun l l' => l.2.2 ≠ l'.2.2 ∧ l.2.1 ≠ l'.1)
    (hM : ∀ l ∈ L, l.1.val = l.2.2.2.val ∧ l.2.2.1 = l.2.1) (v : Fin r × Fin n) :
    eval (lrf_idS R r n) (lrfc_Phi L (X v)) =
      C (idFrame R r n v) + if v ∈ L.map (·.2.2) then X v else 0 := by sorry
