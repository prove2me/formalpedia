-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_nonuniform_neutral_hierarchy
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.nonuniform_neutral_hierarchy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:28:44.320778+00:00
-- url     : https://prove2.me/theorems/039e4f13-78f9-4c85-a165-81c0ead7049e
-- title:
--   Theorem 5.2 — neutral limit generation beyond all finite levels
-- statement:
--   Let $U$ be a countably infinite universe with a global ordering $\prec$ of order type $\omega$. There is a countable collection $C$ of infinite languages over $U$ that is adversarially, and hence neutrally, generatable in the limit without repetition, but is not neutrally $k$-generatable for any finite $k\ge1$, even with repetition.
--
--   $$
--   C \text{ countable},\quad C\in\mathrm{Adv}_{\mathrm{NR}}\cap\mathrm{Neu}_{\mathrm{NR}},\quad C\notin\mathrm{Neu}^{k}_{\mathrm R}\ \text{for every } k\ge1 .
--   $$
--
--   This is clause 2 of Theorem 1.3. The result is unconditional; generatability of countable collections, cited from prior work in the paper, is not assumed.
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} (or a universe with a fixed global ordering u1 ≺ u2 ≺ ⋯) → an arbitrary infinite type U with a linear order in which every element has finitely many predecessors; reason: such a type is exactly an ω-ordered universe, order-isomorphic to (N,<); the statement is the source's under that relabelling
--   - encoding: the enumeration of L induced by ≺ → every full injective enumeration x of L that is strictly increasing; reason: on an ω-ordered universe this enumeration exists and is unique, so ∀ over it is the canonical enumeration
--   - encoding: k ∈ N = {1,2,...}; 'for any finite k' → k : ℕ with 0 < k (inside the generatability predicates, and as ∀ k, 0 < k → …); reason: the paper's N is the positive integers; the predicates are false at k = 0, so nothing outside the source's domain is asserted
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 5.2, printed p.21 (PDF p.22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Neutral
import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Adversarial

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem 5.2, printed p.21 (PDF p.22), on an ω-ordered universe: one countable collection,
adversarially and neutrally generatable in the limit without repetition, that fails every
positive neutral threshold even with repetition. No cited result is assumed. -/
theorem nonuniform_neutral_hierarchy (U : Type) [LinearOrder U] [LocallyFiniteOrderBot U]
    [Infinite U] :
    ∃ C : LanguageCollection U, C.Countable ∧ AdversarialLimitGeneratable .NR C ∧
      NeutralLimitGeneratable .NR C ∧
      ∀ k : ℕ, 0 < k → ¬ NeutralKGeneratable .R C k := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
