-- Prove2me | Theorems.Thm_BundleGerbeStable_theorem_2_1
-- name    : BundleGerbeStable.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:36.599481+00:00
-- url     : https://prove2.me/theorems/523dc2a7-9034-48bb-992b-7ada13f257de
-- title:
--   Theorem 2.1: zero Dixmier-Douady class precisely when trivial
-- statement:
--   A bundle gerbe $(P,Y)$ over a smooth manifold $M$ has zero Dixmier-Douady class precisely when it is trivial:
--   $$d(P)=0\iff P\cong\delta(Q)\text{ for some }\mathbb C^\times\text{ bundle }Q\to Y.$$
--
--   The paper quotes this from Murray's *Bundle gerbes* (1996). It is the step of Proposition 3.2 that passes from a vanishing class back to geometry.
--
--   Differences from the source:
--   - generalization: Y and P in a category of spaces "deduced from context": finite-dimensional manifolds, infinite-dimensional manifolds, differentiable spaces (p.2) → Y and P diffeological spaces in the universe of M, π smooth and locally split, with local triviality by diffeomorphisms; reason: the paper leaves the category open; diffeological spaces contain each named category, and a smooth map between manifolds is a diffeologically smooth one
--   - reading: "a manifold M" → M a finite-dimensional boundaryless smooth manifold of constant model E, Hausdorff and paracompact, with its manifold diffeology; no second countability, compactness or connectedness; reason: the paper's d(P) uses open covers with contractible intersections and H²(M, ℂ×) ≃ H³(M, ℤ) uses smooth partitions of unity; infinite-dimensional spaces occur in the paper as Y, not as this M
--   - encoding: δ(Q) = π₁⁻¹(Q)* ⊗ π₂⁻¹(Q), and trivial = isomorphic to some δ(Q) → a relation IsDelta G Q given by a smooth map c(q₁, q₂) = q₁* ⊗ q₂, and IsTrivial G := ∃ Q, IsDelta G Q; reason: the universal property of the contracted product; IsDelta transports along isomorphisms, so this is the same notion
--   - encoding: H³(M, ℤ), H²(M, ℂ×) (the paper computes with Čech cocycles) → the colimit over covers of Čech cohomology on all tuples, of the presheaves of locally constant ℤ-valued and smooth ℂˣ-valued functions, presented by a direct sum of cocycles modulo coboundaries and refinement; reason: Mathlib's Sheaf.H has no map from Čech cocycles; for paracompact Hausdorff M this colimit is sheaf cohomology
--   - encoding: an open cover with all intersections contractible → any open cover, as a set of open sets, carrying sections s_α and maps σ_αβ; reason: contractibility is used on p.3 only to make the σ_αβ exist, a cover of the paper's kind is one such cover, and the class does not depend on the choice (dd_cocycle_class)
--   - encoding: the class d(P) ∈ H³(M, ℤ), a function of P → a relation IsDixmierDouady P c; reason: that d is well defined is a theorem (dd_cocycle_class, exp_boundary_equiv), which a definition cannot presuppose
--   - encoding: H²(M, ℂ×) ≃ H³(M, ℤ), with no sign fixed → n = +δf where exp(2πi f) = g (IsExpBoundary); reason: the paper fixes none; the choice changes no statement of the mission
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, Theorem 2.1, p.4

import Mathlib
import Definitions.Def_BundleGerbeStable_IsDixmierDouady
import Definitions.Def_BundleGerbeStable_IsDelta

open Manifold ContDiff

namespace BundleGerbeStable

universe u

/-- **Theorem 2.1** (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*, arXiv:math/9908135v1, p.4): a bundle gerbe has zero Dixmier-Douady class precisely when it is
trivial. -/
theorem theorem_2_1 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [ParacompactSpace M] [DiffeologicalSpace M] [IsManifoldDiffeology E M]
    {S : LocallySplit.{u} M} (P : BundleGerbe S) :
    IsDixmierDouady P 0 ↔ IsTrivial P := by sorry

end BundleGerbeStable
