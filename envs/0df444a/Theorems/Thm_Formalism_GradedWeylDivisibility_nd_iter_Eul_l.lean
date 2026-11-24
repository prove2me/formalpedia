-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_nd_iter_Eul_l
-- name    : Formalism.GradedWeylDivisibility.nd_iter_Eul_l
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:45.818334+00:00
-- url     : https://prove2.me/theorems/cc4a7475-0762-4097-a6b0-4888b2fd9c7f
-- title:
--   Graded Weyl Divisibility: nd iter Eul l
-- statement:
--   The Graded Weyl Divisibility construction uses the nd iter Eul l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L50-L57

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

theorem Formalism.GradedWeylDivisibility.nd_iter_Eul_l {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {c : R}
    (hf : ndEul R r n l f = c • f) (k : ℕ) :
    ndEul R r n l ((ndF R r n l j)^[k] f) = (c - k) • (ndF R r n l j)^[k] f := by sorry
