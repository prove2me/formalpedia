-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
-- name    : AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/db4ef324-1d39-5049-add4-9ebc08e95967
-- title:
--   Quotient of a scheme by a finite group acting admissibly
-- statement:
--   Let $X$ be a scheme, $G$ a finite group, and $\rho \colon G \to \operatorname{Aut} X$ a homomorphism into the automorphism group of $X$ in the category of schemes. Assume the action is admissible in the sense that every point $x \in X$ lies in an affine open $U \subseteq X$ with $\rho(g)^{-1}(U) = U$ for all $g \in G$. Then there exist a scheme $Y$ and a morphism $\pi \colon X \to Y$ with $\pi \circ \rho(g) = \pi$ for all $g$, such that: $\pi$ is integral, is affine, and is surjective on underlying points; for points $x, x'$ of $X$ one has $\pi(x) = \pi(x')$ if and only if $x' = \rho(g)(x)$ for some $g \in G$; for every open $V \subseteq Y$ the map $\Gamma(V, \mathcal{O}_Y) \to \Gamma(\pi^{-1}V, \mathcal{O}_X)$ is injective with image exactly the sections fixed by the maps induced on $\Gamma(\pi^{-1}V, \mathcal{O}_X)$ by each $\rho(g)$ (which preserves $\pi^{-1}V$ by invariance of $\pi$); every affine open $U \subseteq X$ with $\rho(g)^{-1}(U) = U$ for all $g$ is $\pi^{-1}V$ for some affine open $V \subseteq Y$; and every morphism $f \colon X \to T$ of schemes with $f \circ \rho(g) = f$ for all $g$ factors as $f = f' \circ \pi$ for a unique $f' \colon Y \to T$.
--
--   This is the existence theorem for the quotient $X/G$ of a scheme by a finite group under the admissibility hypothesis, in the form of SGA 1, Exposé V, Propositions 1.1 and 1.8 (equivalently Mumford's construction in the theory of abelian varieties), the conclusions recording that $\pi$ is integral, affine and surjective, that its fibres are the $G$-orbits, that $\mathcal{O}_Y = (\pi_*\mathcal{O}_X)^G$, that invariant affine opens descend, and that $\pi$ is a categorical quotient. It is used in the construction of coarse and fine moduli schemes for polarised abelian schemes with level structure, and in the derivation of quotients presented as pullbacks for actions with Galois-type properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

universe u v

theorem AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
    {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hadm : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) :
    ∃ (Y : Scheme.{u}) (π : X ⟶ Y) (hπ : ∀ g : G, (ρ g).hom ≫ π = π),
      IsIntegralHom π ∧ IsAffineHom π ∧ Function.Surjective π.base ∧
      (∀ x x' : X, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x') ∧
      (∀ V : Y.Opens, Function.Injective (π.app V)) ∧
      (∀ V : Y.Opens, Set.range (π.app V) =
        {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
          (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s}) ∧
      (∀ U : X.Opens, IsAffineOpen U → (∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) →
        ∃ V : Y.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = U) ∧
      (∀ (T : Scheme.{u}) (f : X ⟶ T), (∀ g : G, (ρ g).hom ≫ f = f) →
        ∃! f' : Y ⟶ T, π ≫ f' = f) := by sorry
