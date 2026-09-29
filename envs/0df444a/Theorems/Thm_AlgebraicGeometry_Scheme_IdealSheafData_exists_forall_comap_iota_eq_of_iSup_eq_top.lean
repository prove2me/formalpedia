-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_comap_iota_eq_of_iSup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/57fc8097-f854-5fe6-a8b3-b89c4b806107
-- title:
--   Quasi-coherent ideal sheaves glue along an open cover
-- statement:
--   Let $Y$ be a scheme (in universe $u$) and let $\iota$ be a type in the same universe $u$. Let $\mathcal{U} : \iota \to Y.\mathrm{Opens}$ be a family of open subsets of $Y$ whose supremum in the lattice of opens is the whole of $Y$, i.e. $\bigsqcup_j \mathcal{U}_j = \top$, so that the $\mathcal{U}_j$ cover $Y$. Suppose given, for each $j$, an element $I_j$ of `IdealSheafData` for the open subscheme $\mathcal{U}_j$ of $Y$, that is, a quasi-coherent ideal sheaf on $\mathcal{U}_j$ in Mathlib's presentation by its ideals on affine opens. Assume the compatibility hypothesis that for all $j, k \in \iota$ the pullbacks (`comap`) of $I_j$ and of $I_k$ along the two open immersions $\mathcal{U}_j \sqcap \mathcal{U}_k \to \mathcal{U}_j$ and $\mathcal{U}_j \sqcap \mathcal{U}_k \to \mathcal{U}_k$ given by `Y.homOfLE` applied to $\inf \le \mathrm{left}$ and $\inf \le \mathrm{right}$ agree. The conclusion asserts the existence of a quasi-coherent ideal sheaf $I_0$ on $Y$ whose pullback along the open immersion $(\mathcal{U}_j).\iota : \mathcal{U}_j \to Y$ equals $I_j$ for every $j$. Only existence is asserted; no uniqueness statement is made here.
--
--   This is Zariski descent (gluing) for quasi-coherent ideal sheaves, equivalently for closed subschemes: closed subschemes of the members of an open cover that agree on the pairwise overlaps arise from a single closed subscheme of the ambient scheme. It is used in the construction of the closed subscheme appearing in [`AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point`](thm.html#AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_comap_iota_eq_of_iSup_eq_top
    {Y : Scheme.{u}} {ι : Type u} (𝒰 : ι → Y.Opens) (h𝒰 : ⨆ j, 𝒰 j = ⊤)
    (I : ∀ j, (𝒰 j : Scheme.{u}).IdealSheafData)
    (hI : ∀ j k, (I j).comap (Y.homOfLE (inf_le_left : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 j)) =
      (I k).comap (Y.homOfLE (inf_le_right : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 k))) :
    ∃ I₀ : Y.IdealSheafData, ∀ j, I₀.comap (𝒰 j).ι = I j := by sorry
