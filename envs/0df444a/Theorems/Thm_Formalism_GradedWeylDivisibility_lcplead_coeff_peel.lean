-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_coeff_peel
-- name    : Formalism.GradedWeylDivisibility.lcplead_coeff_peel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:30.468676+00:00
-- url     : https://prove2.me/theorems/5786fe69-0e91-40bd-a326-d8ca7995815d
-- title:
--   Graded Weyl Divisibility: lcplead coeff peel
-- statement:
--   The Graded Weyl Divisibility construction uses the lcplead coeff peel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCpleadLemmas.lean#L69-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCpleadLemmas.lean#L69-L85

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

theorem Formalism.GradedWeylDivisibility.lcplead_coeff_peel (hlj : l ≠ j) (a0 : Fin r) {ω : Fin r × Fin n →₀ ℕ}
    {g : MvPolynomial (Fin r × Fin n) B}
    (hg : IsWeightedHomogeneous (pairW l j) g ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ g.support) :
    coeff ((m.erase (a0, l)).erase (a0, j)) (peel l j a0 (m (a0, l)) g) = coeff m g := by sorry
