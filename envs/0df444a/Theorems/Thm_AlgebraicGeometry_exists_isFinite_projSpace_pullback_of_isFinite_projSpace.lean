-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isFinite_projSpace_pullback_of_isFinite_projSpace
-- name    : AlgebraicGeometry.exists_isFinite_projSpace_pullback_of_isFinite_projSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/2b3bd59d-499f-5257-a1a0-98b3145aadc7
-- title:
--   Fibre products of schemes finite over projective spaces
-- statement:
--   Let $R$ be a commutative ring and let $X$, $Y$ be schemes (in a fixed universe), equipped with morphisms $f : X \to \operatorname{Spec} R$ and $g : Y \to \operatorname{Spec} R$. Suppose given a natural number $a$ and a morphism $G_X : X \to \operatorname{Proj}$ of the graded ring of homogeneous components of $R[x_0,\dots,x_a]$, i.e. $G_X : X \to \mathbb{P}^a_R$, such that $G_X$ is finite and such that $G_X$ followed by the structure morphism $\mathbb{P}^a_R \to \operatorname{Spec} R$ equals $f$; and likewise a natural number $b$ and a finite morphism $G_Y : Y \to \mathbb{P}^b_R$ whose composite with $\mathbb{P}^b_R \to \operatorname{Spec} R$ equals $g$. The conclusion is that there exist a natural number $K$ and a morphism $G_P : X \times_{\operatorname{Spec} R} Y \to \mathbb{P}^K_R$, from the categorical pullback of $f$ and $g$, such that $G_P$ is finite and $G_P$ followed by the structure morphism $\mathbb{P}^K_R \to \operatorname{Spec} R$ equals the first projection $X \times_{\operatorname{Spec} R} Y \to X$ followed by $f$. No value of $K$ is asserted; the existential leaves it unspecified.
--
--   This is the standard consequence of the Segre embedding: a fibre product over $\operatorname{Spec} R$ of two schemes finite over projective spaces over $R$ is again finite over a projective space over $R$, compatibly with the structure morphisms. It is used in the construction of the group-theoretic data attached to fake elliptic curves in the Čerednik–Drinfeld part of the development, where iterated products of a scheme finite over $\mathbb{P}^r_R$ must be kept within the same class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isFinite_projSpace_pullback_of_isFinite_projSpace.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_isFinite_projSpace_pullback_of_isFinite_projSpace
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (a : ℕ) (GX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (a + 1)) R)) [IsFinite GX] (hGX : GX ≫ ProjSpace.π R a = f)
    (b : ℕ) (GY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (b + 1)) R)) [IsFinite GY] (hGY : GY ≫ ProjSpace.π R b = g) :
    ∃ (K : ℕ) (GP : pullback f g ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (K + 1)) R)),
      IsFinite GP ∧ GP ≫ ProjSpace.π R K = pullback.fst f g ≫ f := by sorry
