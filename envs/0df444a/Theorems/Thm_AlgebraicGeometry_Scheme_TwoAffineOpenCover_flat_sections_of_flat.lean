-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_sections_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/feb04283-a1a4-51b8-a457-5d7b95028fd4
-- title:
--   Sections over an affine open of a flat R-scheme are flat
-- statement:
--   Let $R$ be a commutative ring, let $X$ be a scheme, and let $c \colon X \to \operatorname{Spec} R$ be a morphism of schemes which is flat (the typeclass `Flat c`). Let $U$ be an open subscheme of $X$ and assume $U$ is affine, i.e. `IsAffineOpen U`. Equip the ring $\Gamma(X, U)$ of sections of $\mathcal{O}_X$ over $U$ with the $R$-algebra structure `Scheme.TwoAffineOpenCover.algebraOfHom c U`, namely the one whose structure map is the ring homomorphism underlying the composite of the inverse of the isomorphism $R \xrightarrow{\sim} \Gamma(\operatorname{Spec} R, \mathcal{O})$ with the restriction map $c^{\#} \colon \Gamma(\operatorname{Spec} R, \mathcal{O}) \to \Gamma(X, U)$ attached to $c$ and the inclusion $U \subseteq c^{-1}(\top)$ (`c.appLE ⊤ U le_top`). The assertion is that, for this algebra structure, $\Gamma(X, U)$ is a flat $R$-module.
--
--   This is the affine-local form of flatness of a morphism of schemes: flatness of $c$ transfers to flatness of the rings of sections over affine opens of the source. It supplies the flatness of the terms $\Gamma(X, U_0) \times \Gamma(X, U_1)$ and $\Gamma(X, U_0 \cap U_1)$ of the two-chart Čech complex of a flat scheme over $\operatorname{Spec} R$, and is used throughout the development of relative Picard groups and Euler characteristics built on two-chart affine open covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_sections_of_flat
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) [Flat c]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Flat R Γ(X, U) := by sorry
