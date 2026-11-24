-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_wordOf
-- name    : Formalism.CohomologicalDescent.LR.lrf_wordOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:49.666771+00:00
-- url     : https://prove2.me/theorems/b435b9f1-8e5e-4d17-bf80-401541db7d38
-- title:
--   LR: lrf word Of
-- statement:
--   The LR construction uses the lrf word Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L308-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrfcApplyWordAppendSingle.lean#L308-L319

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

theorem Formalism.CohomologicalDescent.LR.lrf_wordOf (e d : Fin r × Fin n →₀ ℕ) (h : ∀ (a : Fin r) (s : Fin n), s.val < a.val → d (a, s) = e (a, s)) :
    (lrf_L r n).map (fun l => (l.1, l.2.1, d l.2.2)) = wordOf e := by sorry
