-- Prove2me | Theorems.Thm_BundleGerbeStable_product_exists
-- name    : BundleGerbeStable.product_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:09.930464+00:00
-- url     : https://prove2.me/theorems/4da3daff-7be1-4523-9b46-544841cce112
-- title:
--   The product of two bundle gerbes exists
-- statement:
--   Let $(P,Y)$ and $(Q,Z)$ be bundle gerbes over a smooth manifold $M$. There is a bundle gerbe over the fibre product $Y\times_\pi Z$, the **product** $(P\otimes Q,Y\times_\pi Z)$, with fibres
--   $$(P\otimes Q)_{((y_1,z_1),(y_2,z_2))}=P_{(y_1,y_2)}\otimes Q_{(z_1,z_2)}.$$
--
--   The product appears in Theorem 2.2, in the definition of stable isomorphism, and in Proposition 3.2. This statement shows that the relation `IsTensor` is not vacuous.
--
--   Differences from the source:
--   - generalization: Y and P in a category of spaces "deduced from context": finite-dimensional manifolds, infinite-dimensional manifolds, differentiable spaces (p.2) → Y and P diffeological spaces in the universe of M, π smooth and locally split, with local triviality by diffeomorphisms; reason: the paper leaves the category open; diffeological spaces contain each named category, and a smooth map between manifolds is a diffeologically smooth one
--   - reading: "a manifold M" → M a finite-dimensional boundaryless smooth manifold of constant model E, Hausdorff and paracompact, with its manifold diffeology; no second countability, compactness or connectedness; reason: the paper's d(P) uses open covers with contractible intersections and H²(M, ℂ×) ≃ H³(M, ℤ) uses smooth partitions of unity; infinite-dimensional spaces occur in the paper as Y, not as this M
--   - encoding: contracted product P ⊗ Q with its fibres P_(y₁,y₂) ⊗ Q_(z₁,z₂) → a relation IsTensor G P Q, given by a smooth balanced multiplicative map t out of pairs (p, q); reason: the universal property of the contracted product; product_exists gives existence, and G is unique up to isomorphism
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.3

import Mathlib
import Definitions.Def_BundleGerbeStable_IsTensor

open Manifold ContDiff

namespace BundleGerbeStable

universe u

/-- **The product of two bundle gerbes exists** (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*, arXiv:math/9908135v1, §2, p.3): for bundle gerbes `(P, Y)` and
`(Q, Z)` there is a bundle gerbe `(P ⊗ Q, Y ×_π Z)`. -/
theorem product_exists (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [ParacompactSpace M] [DiffeologicalSpace M] [IsManifoldDiffeology E M]
    {S T : LocallySplit.{u} M} (P : BundleGerbe S) (Q : BundleGerbe T) :
    ∃ G : BundleGerbe (fibreProd S T), IsTensor G P Q := by sorry

end BundleGerbeStable
