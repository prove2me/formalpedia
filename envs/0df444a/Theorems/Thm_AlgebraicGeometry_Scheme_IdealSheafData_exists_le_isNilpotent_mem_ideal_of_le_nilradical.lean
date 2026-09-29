-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_le_isNilpotent_mem_ideal_of_le_nilradical
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.exists_le_isNilpotent_mem_ideal_of_le_nilradical
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/803d05fc-4471-57ee-9b0a-f49ad6d7a700
-- title:
--   Nilpotent sub-ideal sheaves exhaust an ideal sheaf inside the nilradical
-- statement:
--   Let $X$ be a scheme whose underlying topological space is quasi-compact and quasi-separated, and let $I$ be an ideal sheaf datum on $X$, that is, an assignment to each affine open $U \subseteq X$ of an ideal $I.\mathrm{ideal}\,U \subseteq \Gamma(X, U)$, compatible with restriction to basic opens in the sense recorded by `Scheme.IdealSheafData`. Assume $I \le X.\mathrm{nilradical}$ in the order on ideal sheaf data, i.e. for every affine open $U$ the ideal $I.\mathrm{ideal}\,U$ is contained in the nilradical of $\Gamma(X, U)$. Let $U$ be an affine open subscheme of $X$ and let $s \in \Gamma(X, U)$ be a section lying in $I.\mathrm{ideal}\,U$. Then there exists an ideal sheaf datum $J$ on $X$ with $J \le I$ (containment of the associated ideals over every affine open), such that $J$ is nilpotent for the multiplication of ideal sheaf data, $J^{n} = \bot$ for some $n$, and such that $s \in J.\mathrm{ideal}\,U$.
--
--   This is the statement that on a quasi-compact quasi-separated scheme a quasi-coherent ideal contained in the nilradical is the directed union of its nilpotent quasi-coherent sub-ideals, every local section being captured by one of them. It is used in the proof of [`AlgebraicGeometry.isAffine_of_isClosedImmersion_of_surjective`](thm.html#AlgebraicGeometry.isAffine_of_isClosedImmersion_of_surjective), where affineness is transferred across a surjective closed immersion by reduction to nilpotent thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_le_isNilpotent_mem_ideal_of_le_nilradical.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_le_isNilpotent_mem_ideal_of_le_nilradical
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : I ≤ X.nilradical) (U : X.affineOpens) (s : Γ(X, U))
    (hs : s ∈ I.ideal U) :
    ∃ J : X.IdealSheafData, J ≤ I ∧ IsNilpotent J ∧ s ∈ J.ideal U := by sorry
