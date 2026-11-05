-- Prove2me | Theorems.Thm_BundleGerbeStable_stable_iso_equivalence
-- name    : BundleGerbeStable.stable_iso_equivalence
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:22.308649+00:00
-- url     : https://prove2.me/theorems/cf9d2578-5aec-4477-9aa5-b88f96b7c6c7
-- title:
--   Stable isomorphism is an equivalence relation
-- statement:
--   On bundle gerbes over members of an admissible class $\mathcal A$ of locally split maps to a smooth manifold $M$, stable isomorphism is reflexive, symmetric and transitive.
--
--   The paper reads this off part (3) of Proposition 3.2. It is what makes "stable isomorphism classes" in Theorem 3.3 meaningful.
--
--   Differences from the source:
--   - generalization: Y and P in a category of spaces "deduced from context": finite-dimensional manifolds, infinite-dimensional manifolds, differentiable spaces (p.2) → Y and P diffeological spaces in the universe of M, π smooth and locally split, with local triviality by diffeomorphisms; reason: the paper leaves the category open; diffeological spaces contain each named category, and a smooth map between manifolds is a diffeologically smooth one
--   - generalization: all bundle gerbes in one context-given category → every admissible class 𝒜 of locally split maps; the trivial gerbes T₁, T₂ range over 𝒜; reason: specializes to the paper: 𝒜 = all locally split maps for diffeological Y, surjective submersions from manifolds for smooth Y; closure under fibre products and refinements by nerves is what the paper's constructions use
--   - reading: "a manifold M" → M a finite-dimensional boundaryless smooth manifold of constant model E, Hausdorff and paracompact, with its manifold diffeology; no second countability, compactness or connectedness; reason: the paper's d(P) uses open covers with contractible intersections and H²(M, ℂ×) ≃ H³(M, ℤ) uses smooth partitions of unity; infinite-dimensional spaces occur in the paper as Y, not as this M
--   - encoding: contracted product P ⊗ Q with its fibres P_(y₁,y₂) ⊗ Q_(z₁,z₂) → a relation IsTensor G P Q, given by a smooth balanced multiplicative map t out of pairs (p, q); reason: the universal property of the contracted product; product_exists gives existence, and G is unique up to isomorphism
--   - encoding: δ(Q) = π₁⁻¹(Q)* ⊗ π₂⁻¹(Q), and trivial = isomorphic to some δ(Q) → a relation IsDelta G Q given by a smooth map c(q₁, q₂) = q₁* ⊗ q₂, and IsTrivial G := ∃ Q, IsDelta G Q; reason: the universal property of the contracted product; IsDelta transports along isomorphisms, so this is the same notion
--   - reading: "P ⊗ T₁ = Q ⊗ T₂" (Definition 3.1) → Nonempty (Iso G₁ G₂), for products G₁, G₂; reason: the proof of Proposition 3.2 writes P ⊗ (Q* ⊗ Q) = Q ⊗ (P ⊗ Q*), whose sides live over different spaces, so literal equality cannot be meant
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §3, p.5

import Mathlib
import Definitions.Def_BundleGerbeStable_StablyIsomorphic

open Manifold ContDiff

namespace BundleGerbeStable

universe u

/-- **Stable isomorphism is an equivalence relation** (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*, arXiv:math/9908135v1, §3, p.5). -/
theorem stable_iso_equivalence (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [ParacompactSpace M] [DiffeologicalSpace M] [IsManifoldDiffeology E M]
    (𝒜 : AdmissibleClass M) :
    Equivalence (StablyIsomorphic 𝒜) := by sorry

end BundleGerbeStable
