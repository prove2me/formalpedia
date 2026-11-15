-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_neutral_limit_imp_active_one
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.neutral_limit_imp_active_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:24:46.497361+00:00
-- url     : https://prove2.me/theorems/57fb4320-215b-41f8-a00d-ea621cf14a38
-- title:
--   Theorem 3.4 — neutral generation implies active 1-generation without repetition
-- statement:
--   Let $U$ be a countably infinite universe with a global ordering $\prec$ of order type $\omega$, and let $C$ be a collection of infinite languages over $U$. If $C$ is neutrally generatable in the limit with repetition, then $C$ is actively $1$-generatable without repetition: there is a generator $G$ such that every $L\in C$ has a full repetition-free enumeration $x_1,x_2,\ldots$ with
--
--   $$
--   G(x_1,\ldots,x_t)\in L\setminus\bigl(\{x_1,\ldots,x_t\}\cup\{G(x_1,\ldots,x_j):1\le j<t\}\bigr)\qquad\text{for all } t\ge1 .
--   $$
--
--   This gives $\mathrm{Neu}_{\mathrm R}\subseteq\mathrm{Act}_{\mathrm{NR}}$ in the strongest form.
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} (or a universe with a fixed global ordering u1 ≺ u2 ≺ ⋯) → an arbitrary infinite type U with a linear order in which every element has finitely many predecessors; reason: such a type is exactly an ω-ordered universe, order-isomorphic to (N,<); the statement is the source's under that relabelling
--   - encoding: the enumeration of L induced by ≺ → every full injective enumeration x of L that is strictly increasing; reason: on an ω-ordered universe this enumeration exists and is unique, so ∀ over it is the canonical enumeration
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem 3.4, printed p.10 (PDF p.11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable
import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Neutral

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem 3.4, printed p.10 (PDF p.11), on an ω-ordered universe. -/
theorem neutral_limit_imp_active_one (U : Type) [LinearOrder U] [LocallyFiniteOrderBot U]
    [Infinite U] (C : LanguageCollection U) (hC : NeutralLimitGeneratable .R C) :
    ActiveKGeneratable .NR C 1 := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
