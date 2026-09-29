-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
-- name    : AlgebraicGeometry.exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/c8bc5802-aff2-5c12-b8bc-a778a6c9667e
-- title:
--   Lifting units of global sections along a surjection of local bases
-- statement:
--   Let $B_1$ be a local commutative ring, $B_0$ a commutative ring, and $\pi : B_1 \to B_0$ a surjective ring homomorphism whose kernel is contained in the maximal ideal of $B_1$. Let $X$ and $X_0$ be schemes, $f : X \to \operatorname{Spec} B_1$, $f_0 : X_0 \to \operatorname{Spec} B_0$ and $g : X_0 \to X$ morphisms such that $g$ followed by $f$ equals $f_0$ followed by $\operatorname{Spec}(\pi)$. Assume further that the two structure morphisms induce bijections on global sections: the composite of the inverse of the counit isomorphism $\Gamma(\operatorname{Spec} B_1, \mathcal O) \cong B_1$ with $f^\sharp$ on the top open, that is the canonical ring map $B_1 \to \Gamma(X, \mathcal O_X)$, is bijective, and likewise $B_0 \to \Gamma(X_0, \mathcal O_{X_0})$ is bijective. Then for every $s \in \Gamma(X_0, \mathcal O_{X_0})$ that is a unit there exists a unit $u \in \Gamma(X, \mathcal O_X)$ whose image under the map on global sections induced by $g$ is exactly $s$.
--
--   This is the unit-lifting step for schemes whose global sections coincide with the base ring (as for abelian schemes), along a surjection of local rings with kernel inside the maximal ideal, i.e. along a thickening of the base. It is used in the construction of isomorphisms of abelian schemes over small extensions, where a candidate isomorphism must be rescaled by a unit of global sections lifted from the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
    {B₁ B₀ : Type} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π) (hI : RingHom.ker π ≤ IsLocalRing.maximalIdeal B₁)
    {X X₀ : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of B₁)) (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X)
    (hg : g ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom π))
    (h₁ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom)
    (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom)
    (s : Γ(X₀, ⊤)) (hs : IsUnit s) :
    ∃ u : Γ(X, ⊤), IsUnit u ∧ g.appTop.hom u = s := by sorry
