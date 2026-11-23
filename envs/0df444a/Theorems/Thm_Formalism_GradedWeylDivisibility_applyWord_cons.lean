-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_applyWord_cons
-- name    : Formalism.GradedWeylDivisibility.applyWord_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:04.331676+00:00
-- url     : https://prove2.me/theorems/ca9279e6-d814-4f13-8c6b-ab22ea4a2b7a
-- title:
--   Graded Weyl Divisibility: apply Word cons
-- statement:
--   The Graded Weyl Divisibility construction uses the apply Word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowdivLemmas.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowdivLemmas.lean#L31-L33

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
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

theorem Formalism.GradedWeylDivisibility.applyWord_cons (R : Type*) [CommRing R] {r n : ℕ} (x : Fin r × Fin r × ℕ)
    (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (x :: w) f = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) := by sorry
