-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_hom_off
-- name    : Formalism.GradedWeylDivisibility.lcplead_hom_off
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:34.309045+00:00
-- url     : https://prove2.me/theorems/3d1223fb-d99c-4657-b02b-3f8abec0fec5
-- title:
--   Graded Weyl Divisibility: lcplead hom off
-- statement:
--   The Graded Weyl Divisibility construction uses the lcplead hom off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCpleadLemmas.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCpleadLemmas.lean#L49-L52

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCpleadLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped MonomialOrder
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {B : Type*} [CommRing B] {r n : ℕ} {l j : Fin n}

theorem Formalism.GradedWeylDivisibility.lcplead_hom_off (hlj : l ≠ j) {ω : Fin r × Fin n →₀ ℕ} {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support)
    (b : Fin r) (t : Fin n) (htl : t ≠ l) (htj : t ≠ j) : m (b, t) = ω (b, t) := by sorry
