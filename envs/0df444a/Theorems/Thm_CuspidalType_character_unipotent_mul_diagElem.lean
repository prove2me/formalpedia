-- Prove2me | Theorems.Thm_CuspidalType_character_unipotent_mul_diagElem
-- name    : CuspidalType.character_unipotent_mul_diagElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/ea1bb839-e823-5a23-b4d9-6e6ff4832d4a
-- title:
--   Vanishing of cuspidal characters on split classes through 1
-- statement:
--   Let $q$ be a prime, let $K$ be a field of characteristic zero, and let $V$ be a finite-dimensional $K$-vector space. Let $\rho$ be a representation of $\mathrm{GL}_2(\mathbb{Z}/q) =$ `GL2 q` (the general linear group of $2\times 2$ matrices over $\mathbb{Z}/q$) on $V$. Assume the cuspidality hypothesis `hcusp`: every $v \in V$ fixed by $\rho(\text{unipotent } t)$ for all $t \in \mathbb{Z}/q$ is zero, where `unipotent q t` is the unit of the matrix ring given by $\begin{pmatrix}1&t\\0&1\end{pmatrix}$ with inverse $\begin{pmatrix}1&-t\\0&1\end{pmatrix}$. Let $a$ be a unit of $\mathbb{Z}/q$ with $a \neq 1$, and let $s \in \mathbb{Z}/q$. Then the character of $\rho$ (the trace of $\rho(g)$ as a $K$-endomorphism of $V$) vanishes at the product $\text{unipotent } s \cdot \text{diagElem } a$, where `diagElem q a` is the unit given by $\begin{pmatrix}a&0\\0&1\end{pmatrix}$ with inverse $\begin{pmatrix}a^{-1}&0\\0&1\end{pmatrix}$; that is, $\operatorname{tr}\rho\begin{pmatrix}a&s\\0&1\end{pmatrix} = 0$.
--
--   This is the vanishing of the character of a cuspidal representation of $\mathrm{GL}_2(\mathbb{F}_q)$ on the split regular semisimple classes having $1$ as an eigenvalue, the case $a \ne 1$ of the classical character table of $\mathrm{GL}_2$ over a finite field. It feeds the analysis of representations satisfying the project's cuspidality predicate, being used by [`CuspidalType.IsCuspidalOfType.exists_linearEquiv_comm_of_isCuspidalOfType`](thm.html#CuspidalType.IsCuspidalOfType.exists_linearEquiv_comm_of_isCuspidalOfType) and by [`CuspidalType.exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central`](thm.html#CuspidalType.exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_character_unipotent_mul_diagElem.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.character_unipotent_mul_diagElem
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (GL2 q) V)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) {a : (ZMod q)ˣ} (ha : a ≠ 1) (s : ZMod q) :
    ρ.character (unipotent q s * diagElem q a) = 0 := by sorry
