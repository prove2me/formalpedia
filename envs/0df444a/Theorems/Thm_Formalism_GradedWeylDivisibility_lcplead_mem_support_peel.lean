-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_mem_support_peel
-- name    : Formalism.GradedWeylDivisibility.lcplead_mem_support_peel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:37.807826+00:00
-- url     : https://prove2.me/theorems/8b27a991-6640-414b-ad42-71aa53175f22
-- title:
--   Graded Weyl Divisibility: lcplead mem support peel
-- statement:
--   The Graded Weyl Divisibility construction uses the lcplead mem support peel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCpleadLemmas.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCpleadLemmas.lean#L87-L94

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

theorem Formalism.GradedWeylDivisibility.lcplead_mem_support_peel (a0 : Fin r) (k : ℕ) {g : MvPolynomial (Fin r × Fin n) B}
    {p : Fin r × Fin n →₀ ℕ} (hp : p ∈ (peel l j a0 k g).support) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ p = (m.erase (a0, l)).erase (a0, j) := by sorry
