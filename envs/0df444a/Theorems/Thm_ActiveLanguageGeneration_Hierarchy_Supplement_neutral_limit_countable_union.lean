-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_neutral_limit_countable_union
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.neutral_limit_countable_union
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:25:46.228286+00:00
-- url     : https://prove2.me/theorems/3ec7439e-2d59-47b9-9eee-d9bc67ad4ae7
-- title:
--   Theorem 3.6 — countable unions preserve neutral generation with repetition
-- statement:
--   Let $C_1,C_2,\ldots$ be a countable sequence of collections of infinite languages over the same universe $U$ with the same global ordering $u_1\prec u_2\prec\cdots$. If every $C_i$ is neutrally generatable in the limit with repetition, then so is
--
--   $$
--   C=\bigcup_{i=1}^{\infty}C_i .
--   $$
--
--   Closure under countable union is what separates neutral from adversarial generation (Theorem 3.8).
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} (or a universe with a fixed global ordering u1 ≺ u2 ≺ ⋯) → an arbitrary infinite type U with a linear order in which every element has finitely many predecessors; reason: such a type is exactly an ω-ordered universe, order-isomorphic to (N,<); the statement is the source's under that relabelling
--   - encoding: the enumeration of L induced by ≺ → every full injective enumeration x of L that is strictly increasing; reason: on an ω-ordered universe this enumeration exists and is unique, so ∀ over it is the canonical enumeration
--   - encoding: C1, C2, … → Cs : ℕ → LanguageCollection U, indexed from 0; reason: zero-based indexing; a finite sequence is covered by repeating a member
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 3.6, printed p.12 (PDF p.13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Neutral

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem 3.6, printed p.12 (PDF p.13): countable unions, over one ω-ordered universe with one
global ordering, preserve neutral generation in the limit with repetition. -/
theorem neutral_limit_countable_union (U : Type) [LinearOrder U] [LocallyFiniteOrderBot U]
    [Infinite U] (Cs : ℕ → LanguageCollection U)
    (hCs : ∀ i, NeutralLimitGeneratable .R (Cs i)) :
    NeutralLimitGeneratable .R (⋃ i, Cs i) := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
