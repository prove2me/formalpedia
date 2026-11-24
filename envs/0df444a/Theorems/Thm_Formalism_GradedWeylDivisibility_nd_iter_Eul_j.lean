-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_nd_iter_Eul_j
-- name    : Formalism.GradedWeylDivisibility.nd_iter_Eul_j
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:51.280357+00:00
-- url     : https://prove2.me/theorems/7ea755c4-ee60-45a0-997e-2a8d7cd9bc5a
-- title:
--   Graded Weyl Divisibility: nd iter Eul j
-- statement:
--   The Graded Weyl Divisibility construction uses the nd iter Eul j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L59-L66

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

theorem Formalism.GradedWeylDivisibility.nd_iter_Eul_j {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {c : R}
    (hf : ndEul R r n j f = c • f) (k : ℕ) :
    ndEul R r n j ((ndF R r n l j)^[k] f) = (c + k) • (ndF R r n l j)^[k] f := by sorry
