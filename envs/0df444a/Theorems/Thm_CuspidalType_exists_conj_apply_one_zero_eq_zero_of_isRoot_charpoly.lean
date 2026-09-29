-- Prove2me | Theorems.Thm_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly
-- name    : CuspidalType.exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/84f41da0-3e5e-5fb7-973d-3afbb1837796
-- title:
--   Eigenvalue in 𝔽_q forces conjugacy into the Borel
-- statement:
--   Let $q$ be a prime and write $\mathrm{GL2}\ q$ for the general linear group $\mathrm{GL}_2(\mathbb{Z}/q)$, realised as the group of units of the ring of $2\times 2$ matrices over $\mathbb{Z}/q$ indexed by `Fin 2`. Let $g$ be an element of this group and let $x \in \mathbb{Z}/q$ be a root of the characteristic polynomial of the underlying matrix of $g$, i.e. $\mathrm{charpoly}$ of the coercion of $g$ to $2\times 2$ matrices evaluates to zero at $x$. The assertion is that there exists $h \in \mathrm{GL}_2(\mathbb{Z}/q)$ such that the matrix underlying $h g h^{-1}$ has vanishing entry in row $1$, column $0$ (indices from $0$), i.e. $g$ is conjugate inside the group to a lower-left-zero, hence upper-triangular, matrix. Only the single entry condition is asserted; the conjugating element is not described further, and no statement is made about the diagonal entries (in particular not that $x$ appears among them).
--
--   This is the non-elliptic half of the standard dichotomy for conjugacy classes in $\mathrm{GL}_2$ over a finite field: an element whose characteristic polynomial has a root in the base field is conjugate into the Borel subgroup of upper-triangular matrices. It is used in the analysis of cuspidal representations of $\mathrm{GL}_2(\mathbb{F}_q)$, in particular by [`CuspidalType.IsCuspidalOfType.exists_charpoly_eq_map_and_charpoly_ind_eq_X_sub_one_sq_mul_map`](thm.html#CuspidalType.IsCuspidalOfType.exists_charpoly_eq_map_and_charpoly_ind_eq_X_sub_one_sq_mul_map), [`CuspidalType.IsCuspidalOfType.exists_linearEquiv_comm_of_isCuspidalOfType`](thm.html#CuspidalType.IsCuspidalOfType.exists_linearEquiv_comm_of_isCuspidalOfType) and [`CuspidalType.sum_character_torus_and_sum_character_torus_mul_character_torus_inv`](thm.html#CuspidalType.sum_character_torus_and_sum_character_torus_mul_character_torus_inv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly
    (q : ℕ) [Fact q.Prime]
    (g : GL2 q) (x : ZMod q)
    (hx : (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x) :
    ∃ h : GL2 q, ((h * g * h⁻¹ : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := by sorry
