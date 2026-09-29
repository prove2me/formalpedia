-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app
-- name    : AlgebraicGeometry.Scheme.Hom.isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/68169314-96c3-5cb7-9acf-b76542dbc0b8
-- title:
--   Immersion criterion from affine charts with surjective sections
-- statement:
--   Let $\varphi : Y \to P$ be a morphism of schemes (both in the bottom universe), let $J$ be a type and let $W : J \to P.\mathrm{Opens}$ be a family of open subsets of $P$ such that: each $W_j$ is an affine open of $P$; each preimage $\varphi^{-1}W_j$ is an affine open of $Y$; the preimages cover the source, in the sense that $\bigsqcup_j \varphi^{-1}W_j = \top$ as open subsets of $Y$; and for each $j$ the ring homomorphism $\varphi^{\sharp}_{W_j} : \Gamma(P, W_j) \to \Gamma(Y, \varphi^{-1}W_j)$ induced by $\varphi$ on sections over $W_j$ is surjective. The conclusion is that $\varphi$ satisfies Mathlib's `IsImmersion`, i.e. $\varphi$ is an immersion: its underlying continuous map is a topological embedding with surjective maps on stalks, and its set-theoretic image is locally closed. Note that the family $(W_j)$ is not assumed to cover $P$; only the preimages are required to cover $Y$, which is why the conclusion is an immersion rather than a closed immersion.
--
--   This is the standard affine-chart criterion for a morphism to be an immersion (a closed immersion into an open subscheme of the target), in the form convenient for checking it on a chart-by-chart description of a morphism. It is used in the construction of an immersion of a scheme into a projective-type target in [`AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`](thm.html#AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.Hom.isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app
    {Y P : Scheme.{0}} (φ : Y ⟶ P) {J : Type} (W : J → P.Opens)
    (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen (φ ⁻¹ᵁ W j))
    (hcov : ⨆ j, φ ⁻¹ᵁ W j = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
    IsImmersion φ := by sorry
