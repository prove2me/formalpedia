-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_tau_iota
-- name    : Formalism.CohomologicalDescent.LR.lrfc_tau_iota
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:59.276307+00:00
-- url     : https://prove2.me/theorems/a2807d7b-ffbe-423a-bade-8b8718358028
-- title:
--   LR: lrfc tau iota
-- statement:
--   The LR construction uses the lrfc tau iota property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L89-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L89-L104

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

theorem Formalism.CohomologicalDescent.LR.lrfc_tau_iota (l : Fin r × Fin r × (Fin r × Fin n)) (F : MvPolynomial (Fin r × Fin n) R) :
    lrfc_tau l (lrfc_iota F) =
      Polynomial.eval₂ lrfc_iota (C (X l.2.2)) (rowGen R l.1 l.2.1 F) := by sorry
