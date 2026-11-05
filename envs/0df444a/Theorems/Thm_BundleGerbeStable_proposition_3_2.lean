-- Prove2me | Theorems.Thm_BundleGerbeStable_proposition_3_2
-- name    : BundleGerbeStable.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:54.16705+00:00
-- url     : https://prove2.me/theorems/5698baa3-e5aa-4fd1-9044-fd0846c63694
-- title:
--   Proposition 3.2: three characterizations of stable isomorphism
-- statement:
--   Let $\mathcal A$ be an admissible class of locally split maps to a smooth manifold $M$. For bundle gerbes $(P,Y)$ and $(Q,Z)$ over members of $\mathcal A$ the following are equivalent:
--
--   1. $P$ and $Q$ are stably isomorphic;
--   2. $P\otimes Q^*$ is trivial;
--   3. $d(P)=d(Q)$.
--
--   This is the core of the paper: stable isomorphism is exactly the relation of having the same Dixmier-Douady class.
--
--   Differences from the source:
--   - generalization: Y and P in a category of spaces "deduced from context": finite-dimensional manifolds, infinite-dimensional manifolds, differentiable spaces (p.2) → Y and P diffeological spaces in the universe of M, π smooth and locally split, with local triviality by diffeomorphisms; reason: the paper leaves the category open; diffeological spaces contain each named category, and a smooth map between manifolds is a diffeologically smooth one
--   - generalization: all bundle gerbes in one context-given category → every admissible class 𝒜 of locally split maps; the trivial gerbes T₁, T₂ range over 𝒜; reason: specializes to the paper: 𝒜 = all locally split maps for diffeological Y, surjective submersions from manifolds for smooth Y; closure under fibre products and refinements by nerves is what the paper's constructions use
--   - reading: "a manifold M" → M a finite-dimensional boundaryless smooth manifold of constant model E, Hausdorff and paracompact, with its manifold diffeology; no second countability, compactness or connectedness; reason: the paper's d(P) uses open covers with contractible intersections and H²(M, ℂ×) ≃ H³(M, ℤ) uses smooth partitions of unity; infinite-dimensional spaces occur in the paper as Y, not as this M
--   - encoding: contracted product P ⊗ Q with its fibres P_(y₁,y₂) ⊗ Q_(z₁,z₂) → a relation IsTensor G P Q, given by a smooth balanced multiplicative map t out of pairs (p, q); reason: the universal property of the contracted product; product_exists gives existence, and G is unique up to isomorphism
--   - encoding: δ(Q) = π₁⁻¹(Q)* ⊗ π₂⁻¹(Q), and trivial = isomorphic to some δ(Q) → a relation IsDelta G Q given by a smooth map c(q₁, q₂) = q₁* ⊗ q₂, and IsTrivial G := ∃ Q, IsDelta G Q; reason: the universal property of the contracted product; IsDelta transports along isomorphisms, so this is the same notion
--   - encoding: H³(M, ℤ), H²(M, ℂ×) (the paper computes with Čech cocycles) → the colimit over covers of Čech cohomology on all tuples, of the presheaves of locally constant ℤ-valued and smooth ℂˣ-valued functions, presented by a direct sum of cocycles modulo coboundaries and refinement; reason: Mathlib's Sheaf.H has no map from Čech cocycles; for paracompact Hausdorff M this colimit is sheaf cohomology
--   - encoding: an open cover with all intersections contractible → any open cover, as a set of open sets, carrying sections s_α and maps σ_αβ; reason: contractibility is used on p.3 only to make the σ_αβ exist, a cover of the paper's kind is one such cover, and the class does not depend on the choice (dd_cocycle_class)
--   - encoding: the class d(P) ∈ H³(M, ℤ), a function of P → a relation IsDixmierDouady P c; reason: that d is well defined is a theorem (dd_cocycle_class, exp_boundary_equiv), which a definition cannot presuppose
--   - encoding: H²(M, ℂ×) ≃ H³(M, ℤ), with no sign fixed → n = +δf where exp(2πi f) = g (IsExpBoundary); reason: the paper fixes none; the choice changes no statement of the mission
--   - reading: "P ⊗ T₁ = Q ⊗ T₂" (Definition 3.1) → Nonempty (Iso G₁ G₂), for products G₁, G₂; reason: the proof of Proposition 3.2 writes P ⊗ (Q* ⊗ Q) = Q ⊗ (P ⊗ Q*), whose sides live over different spaces, so literal equality cannot be meant
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, Proposition 3.2, p.4

import Mathlib
import Definitions.Def_BundleGerbeStable_StablyIsomorphic
import Definitions.Def_BundleGerbeStable_IsDixmierDouady

open Manifold ContDiff

namespace BundleGerbeStable

universe u

/-- **Proposition 3.2** (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*, arXiv:math/9908135v1, p.4): for bundle gerbes `(P, Y)` and `(Q, Z)` the following are
equivalent: (1) `P` and `Q` are stably isomorphic; (2) `P ⊗ Q*` is trivial; (3) `d(P) = d(Q)`.

**Formalization Note.** "`P ⊗ Q*` is trivial" is "there is a product `G` of `P` and `Q*` that is
trivial"; the product exists and is unique up to isomorphism (`product_exists`, `IsTensor`). "`d(P) =
d(Q)`" is "`P` and `Q` have a common class `c`"; each has exactly one (`dd_cocycle_class`,
`exp_boundary_equiv`). -/
theorem proposition_3_2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [ParacompactSpace M] [DiffeologicalSpace M] [IsManifoldDiffeology E M]
    (𝒜 : AdmissibleClass M) (P Q : GerbeOver 𝒜) :
    List.TFAE [
      StablyIsomorphic 𝒜 P Q,
      ∃ G : BundleGerbe (fibreProd P.1.1 Q.1.1), IsTensor G P.2 Q.2.dual ∧ IsTrivial G,
      ∃ c : H3 M, IsDixmierDouady P.2 c ∧ IsDixmierDouady Q.2 c] := by sorry

end BundleGerbeStable
