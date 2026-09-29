-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/e3b3edac-8d2f-5735-9e7c-f314a85037ca
-- title:
--   Affine acyclicity of the alternating Čech complex of 𝒪
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi\colon V\to\operatorname{Spec} R$ a separated morphism. Let $W$ be an open subscheme of $V$ and let $K$ be an ordered affine cover of $W$, that is: a finite linearly ordered index type $\iota$, opens $U_i\subseteq V$ for $i\in\iota$, each $U_i$ affine open and contained in $W$, with $\bigsqcup$-supremum $\bigvee_i U_i = W$. Assume in addition that $W$ itself is an affine open. Fix $p\in\mathbb N$. Each module of sections $\Gamma(V,O)$ is regarded as an $R$-module through the ring homomorphism $R\to\Gamma(V,O)$ obtained by composing the inverse of the canonical isomorphism $R\cong\Gamma(\operatorname{Spec} R,\top)$ with the map $\pi^{\sharp}$ on sections from $\top$ to $O$. With respect to these $R$-module structures, the $R$-linear maps `K.d π p` of the alternating Čech-type complex attached to $\pi$ and $K$ satisfy $\ker(\mathrm{K.d}\,\pi\,(p+1))\le\operatorname{range}(\mathrm{K.d}\,\pi\,p)$; that is, every cocycle in degree $p+1$ of that complex is a coboundary.
--
--   This is the vanishing of the (alternating) Čech cohomology of the structure sheaf in positive degrees for a finite affine cover of an affine open, the separatedness of $\pi$ guaranteeing that the intersections occurring in the complex are again affine. It is the exactness input used by the Leray-type arguments for $\mathcal O$-module presheaves, notably [`AlgebraicGeometry.OModulePresheaf.Leray.rows_exact`](thm.html#AlgebraicGeometry.OModulePresheaf.Leray.rows_exact) and [`AlgebraicGeometry.OModulePresheaf.exists_box_zigzag_of_d_eq_zero_of_isAffineOpen`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_box_zigzag_of_d_eq_zero_of_isAffineOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π] {W : V.Opens} (K : V.OrderedAffineCoverOf W) (hW : IsAffineOpen W) (p : ℕ) : letI := Scheme.OrderedAffineCoverOf.moduleSections π; LinearMap.ker (K.d π (p + 1)) ≤ LinearMap.range (K.d π p) := by sorry
