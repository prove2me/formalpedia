-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_openCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/554e2778-28f9-52c2-86f1-764aae6c3119
-- title:
--   Gluing quasi-coherent ideal sheaves along an open cover
-- statement:
--   Let $X$ be a scheme and let $\mathcal{U}$ be an open cover of $X$, given by an index type $\mathcal{U}.I_0$, schemes $\mathcal{U}.X\,i$ and jointly surjective open immersions $\mathcal{U}.f\,i \colon \mathcal{U}.X\,i \to X$. Suppose given, for each index $i$, ideal sheaf data $I\,i$ on $\mathcal{U}.X\,i$, that is, a quasi-coherent sheaf of ideals of $\mathcal{O}_{\mathcal{U}.X\,i}$ recorded as a compatible family of ideals of the sections over affine opens. Assume the following compatibility: for all indices $i, j$, every scheme $V$ and all morphisms $a \colon V \to \mathcal{U}.X\,i$ and $b \colon V \to \mathcal{U}.X\,j$ whose composites with $\mathcal{U}.f\,i$, respectively $\mathcal{U}.f\,j$, to $X$ agree, the inverse image ideal sheaves agree, $(I\,i).\mathrm{comap}\,a = (I\,j).\mathrm{comap}\,b$. Then there exists ideal sheaf data $I_0$ on $X$ whose inverse image along each $\mathcal{U}.f\,i$ is $I\,i$. Note that the compatibility hypothesis is demanded for every such test scheme $V$, not merely for the fibre product $\mathcal{U}.X\,i \times_X \mathcal{U}.X\,j$, and that only existence, not uniqueness, of $I_0$ is asserted.
--
--   This is the gluing principle for quasi-coherent subsheaves of the structure sheaf: a family of ideal sheaves on the members of an open cover, agreeing on overlaps, descends to an ideal sheaf on the base. It serves as the construction tool behind ideal sheaves assembled locally, and is used for the ideal sheaves on projective space cut out on basic opens, for the sheaf property of relative effective Cartier divisors, and in the study of invertible modules and their coefficient ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.lean

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Cover.Open

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_openCover
    {X : Scheme.{u}} (𝒰 : X.OpenCover) (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ ⦃i j : 𝒰.I₀⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ 𝒰.X i) (b : V ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (I i).comap a = (I j).comap b) :
    ∃ I₀ : X.IdealSheafData, ∀ i, I₀.comap (𝒰.f i) = I i := by sorry
