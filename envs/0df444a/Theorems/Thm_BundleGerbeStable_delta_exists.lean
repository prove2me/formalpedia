-- Prove2me | Theorems.Thm_BundleGerbeStable_delta_exists
-- name    : BundleGerbeStable.delta_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:46.968923+00:00
-- url     : https://prove2.me/theorems/96d6bd52-8ee6-485f-9e0b-6b79443d72bf
-- title:
--   $\delta(Q)$ is a bundle gerbe
-- statement:
--   Let $M$ be a smooth manifold, $\pi:Y\to M$ a locally split map and $Q\to Y$ a principal $\mathbb C^\times$ bundle. There is a bundle gerbe $\delta(Q)$ over $Y$ with
--   $$\delta(Q)_{(y_1,y_2)}=Q^*_{y_1}\otimes Q_{y_2},$$
--   whose product is induced by the natural pairing of $Q_{y_2}$ with $Q^*_{y_2}$.
--
--   This construction supplies the trivial bundle gerbes, and it shows that the relation `IsDelta` is not vacuous.
--
--   Differences from the source:
--   - generalization: Y and P in a category of spaces "deduced from context": finite-dimensional manifolds, infinite-dimensional manifolds, differentiable spaces (p.2) → Y and P diffeological spaces in the universe of M, π smooth and locally split, with local triviality by diffeomorphisms; reason: the paper leaves the category open; diffeological spaces contain each named category, and a smooth map between manifolds is a diffeologically smooth one
--   - reading: "a manifold M" → M a finite-dimensional boundaryless smooth manifold of constant model E, Hausdorff and paracompact, with its manifold diffeology; no second countability, compactness or connectedness; reason: the paper's d(P) uses open covers with contractible intersections and H²(M, ℂ×) ≃ H³(M, ℤ) uses smooth partitions of unity; infinite-dimensional spaces occur in the paper as Y, not as this M
--   - encoding: δ(Q) = π₁⁻¹(Q)* ⊗ π₂⁻¹(Q), and trivial = isomorphic to some δ(Q) → a relation IsDelta G Q given by a smooth map c(q₁, q₂) = q₁* ⊗ q₂, and IsTrivial G := ∃ Q, IsDelta G Q; reason: the universal property of the contracted product; IsDelta transports along isomorphisms, so this is the same notion
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.3

import Mathlib
import Definitions.Def_BundleGerbeStable_IsDelta

open Manifold ContDiff

namespace BundleGerbeStable

universe u

/-- **δ(Q) is a bundle gerbe** (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*, arXiv:math/9908135v1, §2, p.3): for every ℂ× bundle `Q` over `Y` there is a
bundle gerbe `δ(Q)`, with `δ(Q)_(y₁,y₂) = Q*_y₁ ⊗ Q_y₂`.

**Formalization Note.** `M` is a finite-dimensional, Hausdorff, paracompact, boundaryless smooth
manifold (the reading of "manifold" in the paper) and `Y` is any diffeological space with a locally
split map to `M`. -/
theorem delta_exists (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [ParacompactSpace M] [DiffeologicalSpace M] [IsManifoldDiffeology E M]
    (S : LocallySplit.{u} M) (Q : CxBundle S.Y) :
    ∃ G : BundleGerbe S, IsDelta G Q := by sorry

end BundleGerbeStable
