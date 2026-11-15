-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_neutral_limit_countable_union_nr
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.neutral_limit_countable_union_nr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:26:16.575196+00:00
-- url     : https://prove2.me/theorems/714b8ad1-3978-446f-8b20-592cb1df0b31
-- title:
--   Corollary 3.7 — countable unions preserve neutral generation without repetition
-- statement:
--   Let $C_1,C_2,\ldots$ be a countable sequence of collections of infinite languages over the same universe $U$ with the same global ordering $u_1\prec u_2\prec\cdots$. If every $C_i$ is neutrally generatable in the limit without repetition, then so is
--
--   $$
--   C=\bigcup_{i=1}^{\infty}C_i .
--   $$
--
--   This is the no-repetition version of Theorem 3.6 and is the closure property Theorem 3.8 applies.
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} (or a universe with a fixed global ordering u1 ≺ u2 ≺ ⋯) → an arbitrary infinite type U with a linear order in which every element has finitely many predecessors; reason: such a type is exactly an ω-ordered universe, order-isomorphic to (N,<); the statement is the source's under that relabelling
--   - encoding: the enumeration of L induced by ≺ → every full injective enumeration x of L that is strictly increasing; reason: on an ω-ordered universe this enumeration exists and is unique, so ∀ over it is the canonical enumeration
--   - encoding: C1, C2, … → Cs : ℕ → LanguageCollection U, indexed from 0; reason: zero-based indexing; a finite sequence is covered by repeating a member
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Corollary 3.7, printed p.13 (PDF p.14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Neutral

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Corollary 3.7, printed pp.13–14 (PDF pp.14–15): the same closure without repetition. -/
theorem neutral_limit_countable_union_nr (U : Type) [LinearOrder U] [LocallyFiniteOrderBot U]
    [Infinite U] (Cs : ℕ → LanguageCollection U)
    (hCs : ∀ i, NeutralLimitGeneratable .NR (Cs i)) :
    NeutralLimitGeneratable .NR (⋃ i, Cs i) := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
