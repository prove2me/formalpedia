-- Prove2me | Theorems.Thm_CuspidalType_charpoly_ind_diagElem_eq
-- name    : CuspidalType.charpoly_ind_diagElem_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/d0788a8d-a8b1-5d79-bd2d-b48e5bc07d8d
-- title:
--   Characteristic polynomial of diag(a,1) on K[P¹(𝔽_q)]
-- statement:
--   Let $q$ be a prime, let $K$ be a field, and let $a$ be a unit of $\mathbb{Z}/q$ with $a \neq 1$. Write $\mathrm{ProjLine}\,q$ for the projectivization of the $\mathbb{Z}/q$-module $\mathrm{Fin}\,2 \to \mathbb{Z}/q$, i.e. $\mathbb{P}^1(\mathbb{F}_q)$, and let `ind q K` be the permutation representation of $GL_2(\mathbb{F}_q)$ on the space of finitely supported $K$-valued functions $\mathrm{ProjLine}\,q \to_{f} K$, where a group element $g$ acts by pushing forward supports along the map $x \mapsto g \bullet x$. Let `diagElem q a` be the element of $GL_2(\mathbb{F}_q)$ given by the matrix $\mathrm{diag}(a,1)$ together with $\mathrm{diag}(a^{-1},1)$ as its two-sided inverse. The theorem asserts the identity of polynomials in $K[X]$ $$\mathrm{charpoly}\bigl(\mathrm{ind}\,q\,K\,(\mathrm{diagElem}\,q\,a)\bigr) = (X-1)^2\,\bigl(X^{\,\mathrm{ord}(a)} - 1\bigr)^{(q-1)/\mathrm{ord}(a)},$$ where $\mathrm{ord}(a)$ is the multiplicative order of $a$, and the exponent $(q-1)/\mathrm{ord}(a)$ and the subtraction $q-1$ are taken in the natural numbers.
--
--   This records the cycle type of a non-central split semisimple element of $GL_2(\mathbb{F}_q)$ acting on $\mathbb{P}^1(\mathbb{F}_q)$ — two fixed points $[1:0]$, $[0:1]$ and $(q-1)/\mathrm{ord}(a)$ orbits of length $\mathrm{ord}(a)$ on the remaining points — in the form of a characteristic polynomial on the associated permutation module. It feeds the comparison of characteristic polynomials between a representation of cuspidal type and the Steinberg (permutation) representation, used in [`CuspidalType.IsCuspidalOfType.exists_charpoly_eq_map_and_charpoly_ind_eq_X_sub_one_sq_mul_map`](thm.html#CuspidalType.IsCuspidalOfType.exists_charpoly_eq_map_and_charpoly_ind_eq_X_sub_one_sq_mul_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_charpoly_ind_diagElem_eq.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.charpoly_ind_diagElem_eq
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] (a : (ZMod q)ˣ) (ha : a ≠ 1) :
    LinearMap.charpoly (ind q K (diagElem q a)) = (X - 1) ^ 2 * (X ^ orderOf a - 1) ^ ((q - 1) / orderOf a) := by sorry
