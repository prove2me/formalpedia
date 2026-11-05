-- Prove2me | Theorems.Thm_BundleGerbeStable_theorem_3_3
-- name    : BundleGerbeStable.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:23.243077+00:00
-- url     : https://prove2.me/theorems/93ae87cf-4c0e-4d82-8593-b290e3f0d364
-- title:
--   Theorem 3.3: the Dixmier-Douady class is a bijection from stable isomorphism classes of bundle gerbes to $H^3(M,\mathbb Z)$
-- statement:
--   Let $M$ be a finite-dimensional, boundaryless, Hausdorff, paracompact smooth manifold and let $\mathcal A$ be an admissible class of locally split maps to $M$. The Dixmier-Douady class defines a bijection
--   $$\Phi:\{\text{bundle gerbes over members of }\mathcal A\}/\text{stable isomorphism}\;\xrightarrow{\ \simeq\ }\;H^3(M,\mathbb Z).$$
--   Precisely, there is a map $\Phi$ from the stable isomorphism classes to $H^3(M,\mathbb Z)$ such that:
--
--   1. $\Phi$ is bijective;
--   2. for every bundle gerbe $P$ over a member of $\mathcal A$ and every $c\in H^3(M,\mathbb Z)$, $c$ is the Dixmier-Douady class of $P$ if and only if $\Phi[P]=c$;
--   3. two such gerbes have the same class in the quotient if and only if they are stably isomorphic.
--
--   This is the headline result of the paper: bundle gerbes up to stable isomorphism are classified by $H^3(M,\mathbb Z)$, in analogy with line bundles and the Chern class.
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
--   - encoding: stable isomorphism classes → Quot (StablyIsomorphic 𝒜); reason: Quot needs no proof of the equivalence relation; the third clause of the statement and stable_iso_equivalence supply its content
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, Theorem 3.3, p.5

import Mathlib
import Definitions.Def_BundleGerbeStable_StablyIsomorphic
import Definitions.Def_BundleGerbeStable_IsDixmierDouady

open Manifold ContDiff

namespace BundleGerbeStable

universe u

/-- **Theorem 3.3** (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*, arXiv:math/9908135v1, p.5): the Dixmier-Douady class defines a bijection between stable
isomorphism classes of bundle gerbes and `H³(M, ℤ)`. There is a map `Φ` from the stable isomorphism
classes to `H³(M, ℤ)` which is bijective and sends the class of `P` to the Dixmier-Douady class of `P`,
and the classes identify exactly the stably isomorphic pairs.

**Formalization Note.** `M` is a finite-dimensional, boundaryless, Hausdorff, paracompact smooth
manifold; `𝒜` is any admissible class of locally split maps, so the statement specializes to each
category of `Y`'s the paper mentions. `Quot` needs no proof that the relation is an equivalence: the
third clause supplies it, together with `stable_iso_equivalence`. -/
theorem theorem_3_3 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [ParacompactSpace M] [DiffeologicalSpace M] [IsManifoldDiffeology E M]
    (𝒜 : AdmissibleClass M) :
    ∃ Φ : Quot (StablyIsomorphic 𝒜) → H3 M,
      Function.Bijective Φ ∧
      (∀ (P : GerbeOver 𝒜) (c : H3 M),
        IsDixmierDouady P.2 c ↔ Φ (Quot.mk _ P) = c) ∧
      ∀ P Q : GerbeOver 𝒜,
        StablyIsomorphic 𝒜 P Q ↔ Quot.mk (StablyIsomorphic 𝒜) P = Quot.mk _ Q := by sorry

end BundleGerbeStable
