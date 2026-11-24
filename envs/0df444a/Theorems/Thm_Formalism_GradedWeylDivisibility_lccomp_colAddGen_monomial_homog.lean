-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_colAddGen_monomial_homog
-- name    : Formalism.GradedWeylDivisibility.lccomp_colAddGen_monomial_homog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:39.571805+00:00
-- url     : https://prove2.me/theorems/a624bc23-caf8-4a46-96a4-f43d2a6622dc
-- title:
--   Graded Weyl Divisibility: lccomp col Add Gen monomial homog
-- statement:
--   The Graded Weyl Divisibility construction uses the lccomp col Add Gen monomial homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCcompLemmas.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCcompLemmas.lean#L33-L48

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCcompLemmas
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

theorem Formalism.GradedWeylDivisibility.lccomp_colAddGen_monomial_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (d : Fin r × Fin n →₀ ℕ) (a : B) :
    IsWeightedHomogeneous (lccompW l j) (colAddGen B l j (monomial d a))
      (Finsupp.weight (pairW l j) d) := by sorry
