-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ndEul_neg_eq_zero
-- name    : Formalism.GradedWeylDivisibility.ndEul_neg_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:29.888908+00:00
-- url     : https://prove2.me/theorems/72285688-a1c5-4630-80cc-7a85977f9ae7
-- title:
--   Graded Weyl Divisibility: nd Eul neg eq zero
-- statement:
--   The Graded Weyl Divisibility construction uses the nd Eul neg eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LNondomLemmas.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LNondomLemmas.lean#L67-L76

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
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
set_option linter.unusedSimpArgs false
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.ndEul_neg_eq_zero [IsDomain R] [CharZero R] {g : MvPolynomial (Fin r × Fin n) R}
    (s : Fin n) (h : ndEul R r n s g = -g) : g = 0 := by sorry
