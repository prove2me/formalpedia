-- Prove2me | Theorems.Thm_BundleGerbeStable_every_class_realized
-- name    : BundleGerbeStable.every_class_realized
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:40.002442+00:00
-- url     : https://prove2.me/theorems/522ecd49-997e-4842-8350-e1a1925eb1e3
-- title:
--   Every class in $H^3(M,\mathbb Z)$ is a Dixmier-Douady class
-- statement:
--   Let $\mathcal A$ be an admissible class of locally split maps to a smooth manifold $M$. Every $c\in H^3(M,\mathbb Z)$ is the Dixmier-Douady class of some bundle gerbe over a member of $\mathcal A$.
--
--   The paper quotes this from Murray's *Bundle gerbes* (1996). It gives the surjectivity in Theorem 3.3.
--
--   Differences from the source:
--   - generalization: Y and P in a category of spaces "deduced from context": finite-dimensional manifolds, infinite-dimensional manifolds, differentiable spaces (p.2) → Y and P diffeological spaces in the universe of M, π smooth and locally split, with local triviality by diffeomorphisms; reason: the paper leaves the category open; diffeological spaces contain each named category, and a smooth map between manifolds is a diffeologically smooth one
--   - generalization: all bundle gerbes in one context-given category → every admissible class 𝒜 of locally split maps; the trivial gerbes T₁, T₂ range over 𝒜; reason: specializes to the paper: 𝒜 = all locally split maps for diffeological Y, surjective submersions from manifolds for smooth Y; closure under fibre products and refinements by nerves is what the paper's constructions use
--   - reading: "a manifold M" → M a finite-dimensional boundaryless smooth manifold of constant model E, Hausdorff and paracompact, with its manifold diffeology; no second countability, compactness or connectedness; reason: the paper's d(P) uses open covers with contractible intersections and H²(M, ℂ×) ≃ H³(M, ℤ) uses smooth partitions of unity; infinite-dimensional spaces occur in the paper as Y, not as this M
--   - encoding: H³(M, ℤ), H²(M, ℂ×) (the paper computes with Čech cocycles) → the colimit over covers of Čech cohomology on all tuples, of the presheaves of locally constant ℤ-valued and smooth ℂˣ-valued functions, presented by a direct sum of cocycles modulo coboundaries and refinement; reason: Mathlib's Sheaf.H has no map from Čech cocycles; for paracompact Hausdorff M this colimit is sheaf cohomology
--   - encoding: an open cover with all intersections contractible → any open cover, as a set of open sets, carrying sections s_α and maps σ_αβ; reason: contractibility is used on p.3 only to make the σ_αβ exist, a cover of the paper's kind is one such cover, and the class does not depend on the choice (dd_cocycle_class)
--   - encoding: the class d(P) ∈ H³(M, ℤ), a function of P → a relation IsDixmierDouady P c; reason: that d is well defined is a theorem (dd_cocycle_class, exp_boundary_equiv), which a definition cannot presuppose
--   - encoding: H²(M, ℂ×) ≃ H³(M, ℤ), with no sign fixed → n = +δf where exp(2πi f) = g (IsExpBoundary); reason: the paper fixes none; the choice changes no statement of the mission
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §3, p.5

import Mathlib
import Definitions.Def_BundleGerbeStable_StablyIsomorphic
import Definitions.Def_BundleGerbeStable_IsDixmierDouady

open Manifold ContDiff

namespace BundleGerbeStable

universe u

/-- **Every class is realized** (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*, arXiv:math/9908135v1, §3, p.5): every class in `H³(M, ℤ)` is the Dixmier-Douady
class of some bundle gerbe, here over a member of the admissible class `𝒜`. The nerve clause of
`AdmissibleClass` is what makes this hold for every `𝒜`. -/
theorem every_class_realized (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [ParacompactSpace M] [DiffeologicalSpace M] [IsManifoldDiffeology E M]
    (𝒜 : AdmissibleClass M) (c : H3 M) :
    ∃ P : GerbeOver 𝒜, IsDixmierDouady P.2 c := by sorry

end BundleGerbeStable
