-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_neutral_generation_hierarchy
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.neutral_generation_hierarchy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:23:09.404555+00:00
-- url     : https://prove2.me/theorems/9f7f1ded-e03f-4790-9643-f06d48df5d6c
-- title:
--   Theorem 1.3 — neutral generation hierarchy (both clauses)
-- statement:
--   Let $U$ be a countably infinite universe with a global ordering $\prec$ of order type $\omega$. Then:
--
--   1. for every $k\ge2$ there is a collection $C$ that is neutrally $k$-generatable without repetition but not neutrally $(k-1)$-generatable even with repetition;
--   2. there is a countable collection $C$ that is neutrally and adversarially generatable in the limit without repetition but is not neutrally $k$-generatable for any finite $k\ge1$, even with repetition.
--
--   $$
--   \forall k\ge2\ \exists C:\ C\in\mathrm{Neu}^{k}_{\mathrm{NR}}\setminus\mathrm{Neu}^{k-1}_{\mathrm R},\qquad
--   \exists C \text{ countable}:\ C\in\mathrm{Neu}_{\mathrm{NR}}\cap\mathrm{Adv}_{\mathrm{NR}},\ C\notin\textstyle\bigcup_{k\ge1}\mathrm{Neu}^{k}_{\mathrm R}.
--   $$
--
--   This is the neutral counterpart of the mission's goal, the active hierarchy (Theorem 1.2).
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} (or a universe with a fixed global ordering u1 ≺ u2 ≺ ⋯) → an arbitrary infinite type U with a linear order in which every element has finitely many predecessors; reason: such a type is exactly an ω-ordered universe, order-isomorphic to (N,<); the statement is the source's under that relabelling
--   - encoding: k ∈ N = {1,2,...}; 'for any finite k' → k : ℕ with 0 < k (inside the generatability predicates, and as ∀ k, 0 < k → …); reason: the paper's N is the positive integers; the predicates are false at k = 0, so nothing outside the source's domain is asserted
--   - encoding: the enumeration of L induced by ≺ → every full injective enumeration x of L that is strictly increasing; reason: on an ω-ordered universe this enumeration exists and is unique, so ∀ over it is the canonical enumeration
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 1.3, printed p.2 (PDF p.3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Neutral
import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Adversarial

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem 1.3, both clauses, printed pp.2–3 (PDF pp.3–4), on an ω-ordered universe. -/
theorem neutral_generation_hierarchy (U : Type) [LinearOrder U] [LocallyFiniteOrderBot U]
    [Infinite U] :
    (∀ k : ℕ, 2 ≤ k → ∃ C : LanguageCollection U,
      NeutralKGeneratable .NR C k ∧ ¬ NeutralKGeneratable .R C (k - 1)) ∧
    (∃ C : LanguageCollection U, C.Countable ∧ NeutralLimitGeneratable .NR C ∧
      AdversarialLimitGeneratable .NR C ∧
      ∀ k : ℕ, 0 < k → ¬ NeutralKGeneratable .R C k) := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
