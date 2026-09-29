-- Prove2me | Theorems.Thm_CuspidalType_eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero
-- name    : CuspidalType.eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/8185a890-1bff-5cb6-842c-d3bcd17825cd
-- title:
--   Upper-triangular elements of GL₂(𝔽_q) in normal form
-- statement:
--   Let $q$ be a prime and let $b$ be an element of `GL2 q`, the general linear group of $2\times 2$ matrices over $\mathbb{Z}/q$, whose underlying matrix has vanishing $(1,0)$ entry, i.e. $b$ is upper triangular. Then one of two alternatives holds. Either there are a unit $c$ of $\mathbb{Z}/q$ and a scalar $t \in \mathbb{Z}/q$ with $b = \mathrm{scalarElem}(c)\cdot \mathrm{unipotent}(t)$, where $\mathrm{scalarElem}(c)$ is the image of $c$ under the unit map induced by the scalar ring homomorphism, namely the matrix $c\,I_2$, and $\mathrm{unipotent}(t)$ is the invertible matrix $\begin{pmatrix}1&t\\0&1\end{pmatrix}$ with inverse $\begin{pmatrix}1&-t\\0&1\end{pmatrix}$; or there are units $a$, $d$ of $\mathbb{Z}/q$ and a scalar $s \in \mathbb{Z}/q$ with $a \neq d$ as units and $b = \mathrm{unipotent}(s)\cdot\bigl(\mathrm{scalarElem}(d)\cdot \mathrm{diagElem}(a d^{-1})\bigr)$, where $\mathrm{diagElem}(u)$ denotes the invertible matrix $\begin{pmatrix}u&0\\0&1\end{pmatrix}$ with inverse $\begin{pmatrix}u^{-1}&0\\0&1\end{pmatrix}$. Thus an upper-triangular element is either a scalar times a unipotent, or a unipotent times a diagonal element with distinct diagonal entries. For $q=2$ the second alternative cannot occur.
--
--   This is the normal form for elements of the standard Borel subgroup of $\mathrm{GL}_2(\mathbb{F}_q)$, written in terms of the three families of group elements (scalar, unipotent, diagonal) used in the local analysis of cuspidal types, so that character values on conjugacy-class representatives can be read off directly. It is used in the cuspidal-type development, notably in the determination of characteristic polynomials of such elements, in the construction of an equivariant linear equivalence for representations of cuspidal type, and in the evaluation of character sums over the diagonal torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero
    (q : ℕ) [Fact q.Prime]
    (b : GL2 q) (hb : (b : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0) :
    (∃ (c : (ZMod q)ˣ) (t : ZMod q), b = scalarElem q c * unipotent q t) ∨
    (∃ (a d : (ZMod q)ˣ) (s : ZMod q), a ≠ d ∧ b = unipotent q s * (scalarElem q d * diagElem q (a * d⁻¹))) := by sorry
