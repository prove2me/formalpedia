-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_active_k_density_one
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.active_k_density_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:32:45.886436+00:00
-- url     : https://prove2.me/theorems/dd209145-bd85-4c75-8098-302f101ed999
-- title:
--   Theorem D.3 — active k-generation with lower density 1
-- statement:
--   Let $U$ be a countably infinite universe with a global ordering $\prec$ of order type $\omega$, $C$ a collection of infinite languages over $U$ and $k\ge1$. If $C$ is actively $k$-generatable (with repetition), then $C$ is actively $k$-generatable with lower density $1$: one generator $G$ has, for every $K\in C$, a single full repetition-free enumeration $E$ on which it is correct at every time $t\ge k$ and
--
--   $$
--   \mu_{\mathrm{low}}\bigl(O(E,G),K\bigr)\ge1 .
--   $$
--
--   Uniform active generation can thus always be made to have full breadth.
--
--   Differences from the source:
--   - encoding: universe N = {1,2,...} (or a universe with a fixed global ordering u1 ≺ u2 ≺ ⋯) → an arbitrary infinite type U with a linear order in which every element has finitely many predecessors; reason: such a type is exactly an ω-ordered universe, order-isomorphic to (N,<); the statement is the source's under that relabelling
--   - reading: actively k-generatable with lower density 1 (not separately defined) → one generator, and per target one enumeration with correctness at every t ≥ k (Definition 2.2, R) and lower density ≥ 1 of all outputs (Definition D.1 item 2); reason: the only reading the proof establishes and the natural combination of the two definitions
--   - encoding: µlow(O(E,G), K) ≥ 1, a liminf → for every ε > 0, eventually |{i < n : ℓ_i ∈ O(E,G)}| / n ≥ 1 − ε along the ≺-ordered listing of K, with O(E,G) = Set.range (outputAt G x); reason: for a [0,1]-valued sequence liminf ≥ α iff this ε-form holds; it avoids Filter.liminf's junk value; the outputs are those at every time t ≥ 1
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Theorem D.3, printed p.37 (PDF p.38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable
import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_LowerDensity

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Theorem D.3, printed p.37 (PDF p.38), on an ω-ordered universe: active `k`-generation
(with repetition) implies active `k`-generation with lower density 1. -/
theorem active_k_density_one (U : Type) [LinearOrder U] [LocallyFiniteOrderBot U]
    [Infinite U] (C : LanguageCollection U) (k : ℕ) (hC : ActiveKGeneratable .R C k) :
    ActiveKGeneratableWithDensity C k 1 := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
