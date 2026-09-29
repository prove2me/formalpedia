-- Prove2me | Theorems.Thm_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq
-- name    : CuspForm.eq_zero_of_forall_vadd_inv_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/deb4da6c-e91d-5fcc-acfc-cda71eedad0e
-- title:
--   Cusp form periodic under all q'^{-j} vanishes
-- statement:
--   Let $R$ and $q'$ be natural numbers with $R \neq 0$ and $1 < q'$, let $k$ be an integer, and let $y$ be a cusp form of weight $k$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ obtained as the image of the congruence subgroup $\Gamma_0(R) \le \mathrm{SL}_2(\mathbb{Z})$ under the natural map into $\mathrm{GL}_2(\mathbb{R})$; thus $y \colon \mathbb{H} \to \mathbb{C}$ is holomorphic, weight-$k$ invariant under that group, and vanishes at the cusps in the sense of Mathlib's `CuspForm`. Assume that for every natural number $j$ and every $\tau$ in the upper half-plane one has $y\bigl((q'^{j})^{-1} +_{v} \tau\bigr) = y(\tau)$, where $(q'^{j})^{-1}$ is the real number $1/q'^{j}$ acting on $\mathbb{H}$ by horizontal translation, i.e. $y(\tau + q'^{-j}) = y(\tau)$ for all $j \ge 0$. The conclusion is that $y = 0$ as an element of the space of cusp forms. (The case $j = 0$ of the hypothesis is vacuous, being the translation invariance by $1$ already implied by $\Gamma_0(R)$-invariance.)
--
--   This is the elementary Fourier-analytic vanishing statement that a cusp form on $\Gamma_0(R)$ admitting all the periods $q'^{-j}$, $j \ge 0$, must vanish: periodicity by $q'^{-j}$ forces the $n$-th $q$-expansion coefficient to vanish unless $q'^{j} \mid n$, and letting $j$ grow kills every coefficient. It is used by [`CuspForm.eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero`](thm.html#CuspForm.eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero) and [`CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1`](thm.html#CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1) as the injectivity input in the study of cusp forms under the diagonal Hecke matrices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem CuspForm.eq_zero_of_forall_vadd_inv_pow_eq
    {R q' : ℕ} [NeZero R] (hq' : 1 < q') (k : ℤ)
    (y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (h : ∀ (j : ℕ) (τ : ℍ), y ((((q' : ℝ) ^ j)⁻¹) +ᵥ τ) = y τ) :
    y = 0 := by sorry
