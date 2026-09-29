-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one
-- name    : CerednikDrinfeld.Omega.v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/af68b33d-a36e-50ce-b281-ee5cf764ee11
-- title:
--   Units of holOn on the level-0 affinoid have constant valuation
-- statement:
--   Let $K_0$ be a field and $K$ an algebraically closed field which is a $K_0$-algebra, equipped with a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi_1$ be a pseudo-uniformiser, i.e. an element $\varpi\in K_0$ whose image in $K$ satisfies $0<v(\varpi)<1$ and such that every nonzero $a\in K_0$ admits $N\in\mathbb{N}$ with $v(\varpi)^N\le v(a)\le v(\varpi)^{-N}$. Write $\Omega_0=\mathrm{affinoid}\ \varpi_1\ 0$ for the set of $z\in K$ with $v(z)\le 1$ and $v(z-a)\ge 1$ for every $a\in K_0$ with $v(a)\le 1$. Let $f,g:\Omega_0\to K$ both lie in the subring $\mathrm{holOn}$, that is: each is a uniform limit on $\Omega_0$ of a sequence of rational functions $r_k$ (given as numerator/denominator pairs) whose denominators do not vanish on $\Omega_0$ and whose values on $\Omega_0$ are bounded in valuation by a single element of $K$, uniformly in $k$. Assume $fg=1$ in the ring of $K$-valued functions on $\Omega_0$. Then $v(f(z))=v(f(z'))$ for all $z,z'\in\Omega_0$.
--
--   This is the statement that a unit of the ring of rigid holomorphic functions on the standard vertex fibre $\Omega_0$ of the Drinfeld upper half plane has constant valuation, the basic input for the multiplicative theory of theta functions on Mumford curves. It is used in the construction of the theta products and of the valuation homomorphism measuring the behaviour of units under the action of the group, via results such as [`CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt`](thm.html#CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt) and [`CerednikDrinfeld.Omega.exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder`](thm.html#CerednikDrinfeld.Omega.exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K] [IsAlgClosed K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ₁ : PseudoUniformizer K₀ K)
    {f g : ↥(affinoid ϖ₁ 0) → K} (hf : f ∈ holOn K (affinoid ϖ₁ 0)) (hg : g ∈ holOn K (affinoid ϖ₁ 0))
    (hfg : f * g = 1) (z z' : ↥(affinoid ϖ₁ 0)) :
    Valued.v (f z) = Valued.v (f z') := by sorry
