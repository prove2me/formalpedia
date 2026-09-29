-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/938ad2b3-81f0-5322-ada3-b0e7e7de3e07
-- title:
--   Ideal sheaves agreeing on an open cover are equal
-- statement:
--   Let $X$ be a scheme (in universe $u$) and let $\mathcal{U}$ be an open cover of $X$ in Mathlib's sense: a family of schemes $\mathcal{U}.X\,i$ together with open immersions $\mathcal{U}.f\,i : \mathcal{U}.X\,i \to X$ whose images cover the underlying space of $X$. Let $I$ and $J$ be two elements of `X.IdealSheafData`, that is, two quasi-coherent sheaves of ideals on $X$ presented by the data of an ideal of $\Gamma(X, U)$ for every affine open $U \subseteq X$, compatible with passage to basic opens. Assume that for every index $i$ the inverse image ideal sheaves along $\mathcal{U}.f\,i$ agree, $I.\mathrm{comap}(\mathcal{U}.f\,i) = J.\mathrm{comap}(\mathcal{U}.f\,i)$. The conclusion is that $I = J$. No hypothesis is imposed on $X$ beyond its being a scheme, and no affineness or quasi-compactness is required of the members of the cover.
--
--   This is the uniqueness half of the statement that quasi-coherent ideal sheaves glue along an open cover: an ideal sheaf is determined by its inverse images on the members of a cover. It is used in the treatment of relative effective Cartier divisors and of the relative Picard group, for instance to check that two such divisors on a scheme over a base coincide after verifying the identity locally on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq.lean

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Cover.Open

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J := by sorry
