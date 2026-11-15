-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_active_limit_density_one
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.active_limit_density_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:32:07.955177+00:00
-- url     : https://prove2.me/theorems/75e7c31e-603a-4fab-ba3b-d3f5b81be188
-- title:
--   Theorem D.2 — active generation in the limit with lower density 1
-- statement:
--   Let $U$ be a countably infinite universe with a global ordering $\prec$ of order type $\omega$. Every collection $C$ of infinite languages over $U$, countable or not, is actively generatable in the limit with lower density $1$: there is one generator $G$ such that every $K\in C$ has a single full repetition-free enumeration $E$ on which $G$ is eventually correct (with repetition) and the set $O(E,G)$ of all its outputs satisfies
--
--   $$
--   \mu_{\mathrm{low}}\bigl(O(E,G),K\bigr)\ge1 .
--   $$
--
--   It strengthens Theorem 3.1 from correctness to full breadth.
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} (or a universe with a fixed global ordering u1 ≺ u2 ≺ ⋯) → an arbitrary infinite type U with a linear order in which every element has finitely many predecessors; reason: such a type is exactly an ω-ordered universe, order-isomorphic to (N,<); the statement is the source's under that relabelling
--   - encoding: µlow(O(E,G), K) ≥ 1, a liminf → for every ε > 0, eventually |{i < n : ℓ_i ∈ O(E,G)}| / n ≥ 1 − ε along the ≺-ordered listing of K, with O(E,G) = Set.range (outputAt G x); reason: for a [0,1]-valued sequence liminf ≥ α iff this ε-form holds; it avoids Filter.liminf's junk value; the outputs are those at every time t ≥ 1
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem D.2, printed p.36 (PDF p.37); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_LowerDensity

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem D.2, printed p.36 (PDF p.37), on an ω-ordered universe. -/
theorem active_limit_density_one (U : Type) [LinearOrder U] [LocallyFiniteOrderBot U]
    [Infinite U] (C : LanguageCollection U) : ActiveLimitGeneratableWithDensity C 1 := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
