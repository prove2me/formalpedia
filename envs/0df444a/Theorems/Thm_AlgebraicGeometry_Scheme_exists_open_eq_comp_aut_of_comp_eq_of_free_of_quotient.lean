-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient
-- name    : AlgebraicGeometry.Scheme.exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/1fcd5f7b-e7a3-54c9-ac94-88910016b69a
-- title:
--   Local rigidity of T-points of a free finite quotient
-- statement:
--   Let $X$ and $Y$ be schemes, $G$ a finite group and $\rho : G \to \operatorname{Aut} X$ a group homomorphism, and assume: (admissibility) every point of $X$ lies in an affine open $U \subseteq X$ with $(\rho g)^{-1}(U) = U$ for all $g \in G$; there is a morphism $\pi : X \to Y$ with $\rho(g)$ followed by $\pi$ equal to $\pi$ for every $g$, such that $\pi$ is an affine morphism, surjective on underlying points, its fibres are exactly the $G$-orbits ($\pi(x) = \pi(x')$ iff $x' = \rho(g)(x)$ for some $g$), and for every open $V \subseteq Y$ the map $\pi^{\sharp} : \Gamma(Y, V) \to \Gamma(X, \pi^{-1}V)$ is injective with image precisely the sections fixed by the action of every $g \in G$ on $\Gamma(X, \pi^{-1}V)$ (via the identification $(\rho g)^{-1}(\pi^{-1}V) = \pi^{-1}V$); and (freeness on field-valued points) for every field $K$, every morphism $x : \operatorname{Spec} K \to X$ and every $g \in G$, $x$ followed by $\rho(g)$ equal to $x$ forces $g = 1$. Then two conclusions hold. First, for every scheme $T$ and morphisms $t_1, t_2 : T \to X$ with $t_1$ followed by $\pi$ equal to $t_2$ followed by $\pi$, and every point $p$ of $T$, there are $g \in G$ and an open $U \subseteq T$ containing $p$ such that the restrictions to $U$ satisfy $t_2|_U = \rho(g) \circ t_1|_U$. Second, for every scheme $T$, every $t : T \to X$ and every $g \in G$, if $T$ is non-empty and $t$ followed by $\rho(g)$ equals $t$, then $g = 1$.
--
--   This is the torsor property of a free finite quotient $\pi : X \to Y = X/G$, in the pointwise-local form: on suitable neighbourhoods any two $T$-points of $X$ lying over the same $T$-point of $Y$ differ by a single group element, uniquely so, which is the content of the classical isomorphism $X \times_Y X \cong \coprod_{g \in G} X$. It is derived from the affine Galois-descent description of $\Gamma(X, \pi^{-1}V)$ over an affine open $V \subseteq Y$ given by [`AlgebraicGeometry.Scheme.exists_ringAut_galois_sections_of_free_of_quotient`](thm.html#AlgebraicGeometry.Scheme.exists_ringAut_galois_sections_of_free_of_quotient), and feeds into [`AlgebraicGeometry.Scheme.finite_flat_and_locally_eq_comp_of_free_of_quotient`](thm.html#AlgebraicGeometry.Scheme.finite_flat_and_locally_eq_comp_of_free_of_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient
    {X Y : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hadm : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U)
    (π : X ⟶ Y) (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (hfib : ∀ x x' : X, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hinj : ∀ V : Y.Opens, Function.Injective (π.app V))
    (hrange : ∀ V : Y.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (hfree : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ X) (g : G), x ≫ (ρ g).hom = x → g = 1) :
    (∀ {T : Scheme.{u}} (t₁ t₂ : T ⟶ X), t₁ ≫ π = t₂ ≫ π →
      ∀ p : T, ∃ (g : G) (U : T.Opens), p ∈ U ∧ U.ι ≫ t₂ = U.ι ≫ t₁ ≫ (ρ g).hom) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ X) (g : G), Nonempty T → t ≫ (ρ g).hom = t → g = 1) := by sorry
