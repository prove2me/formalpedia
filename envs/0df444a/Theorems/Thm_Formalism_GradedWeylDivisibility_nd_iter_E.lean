-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_nd_iter_E
-- name    : Formalism.GradedWeylDivisibility.nd_iter_E
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:29.880527+00:00
-- url     : https://prove2.me/theorems/e47418e7-40a4-4c14-a226-3342010ba9b8
-- title:
--   Graded Weyl Divisibility: nd iter E
-- statement:
--   The Graded Weyl Divisibility construction uses the nd iter E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L68-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L68-L83

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
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
open Formalism Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.nd_iter_E {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {cl cj : R}
    (hl : ndEul R r n l f = cl • f) (hj : ndEul R r n j f = cj • f) (hE : ndE R r n l j f = 0)
    (k : ℕ) :
    ndE R r n l j ((ndF R r n l j)^[k + 1] f) =
      (((k : R) + 1) * (cl - cj - k)) • (ndF R r n l j)^[k] f := by sorry
