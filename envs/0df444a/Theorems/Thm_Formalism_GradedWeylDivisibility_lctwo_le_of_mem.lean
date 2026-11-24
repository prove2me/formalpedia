-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lctwo_le_of_mem
-- name    : Formalism.GradedWeylDivisibility.lctwo_le_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:36.083293+00:00
-- url     : https://prove2.me/theorems/61606749-d771-42ef-aedd-1119abdfbe91
-- title:
--   Graded Weyl Divisibility: lctwo le of mem
-- statement:
--   The Graded Weyl Divisibility construction uses the lctwo le of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TwoColumn.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TwoColumn.lean#L33-L39

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TwoColumn
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

theorem Formalism.GradedWeylDivisibility.lctwo_le_of_mem {B : Type*} [CommRing B] {r n : ℕ} {l j : Fin n} (hlj : l ≠ j)
    {ω : Fin r × Fin n →₀ ℕ} {p : MvPolynomial (Fin r × Fin n) B}
    (hp : IsWeightedHomogeneous (pairW l j) p ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ p.support) (b : Fin r) :
    m (b, l) ≤ ω (b, l) ∧ m (b, j) ≤ ω (b, l) := by sorry
