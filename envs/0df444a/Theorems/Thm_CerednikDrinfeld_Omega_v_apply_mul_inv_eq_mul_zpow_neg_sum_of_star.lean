-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star
-- name    : CerednikDrinfeld.Omega.v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/06dd4d7a-17f1-53d8-9978-8dac6396f6ad
-- title:
--   Star formulas on overlapping stars differ by a power of v(varpi)
-- statement:
--   Let $K_0$ be a field and $K$ an algebraically closed $K_0$-algebra field carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi\in K_0$ with $0<v(\varpi)<1$ such that every nonzero $a\in K_0$ satisfies $v(\varpi)^N\le v(a)\le v(\varpi)^{-N}$ for some $N\in\mathbb{N}$; assume moreover that for every $a\in K_0$ either $v(a)\le v(\varpi)$ or $1\le v(a)$. Let $T$ be a finite subset of $K_0$ with $v(t)\le1$ for $t\in T$, such that every $a\in K_0$ with $v(a)\le 1$ has some $t\in T$ with $v(a-t)<1$, and $1\le v(t-t')$ for distinct $t,t'\in T$. Let $F:K\to K$ be any function, $c_0,c_0'\in\Gamma_0$ and $m,m':K_0\to\mathbb{Z}$, and assume two star formulas: $v(F(z))=c_0\prod_{t\in T}v(z-t)^{m(t)}$ whenever $v(z-t)>v(\varpi)$ for all $t\in T$ and $v(z)<v(\varpi)^{-1}$, and $v(F(w\varpi^{-1}))=c_0'\prod_{t\in T}v(w-t)^{m'(t)}$ under the same two conditions on $w$. Then for all $w,w'$ with $v(\cdot)\le1$ and $1\le v(\cdot-a)$ for every $a\in K_0$ with $v(a)\le1$ (membership in `affinoid ϖ 0`), one has $v(F(w\varpi^{-1}))=v(F(w'))\cdot v(\varpi)^{-\sum_{t\in T}m(t)}$.
--
--   This is the edge step in the valuation-theoretic analysis of functions on the Drinfeld upper half plane: the standard star and its translate by $\varpi$ overlap in an annulus, and comparing the two star formulas there pins down the ratio of the values of $F$ on the two vertex affinoids as an integral power of $v(\varpi)$. It is used in the construction of the integer-valued data attached to $F$ on the tree and in the divisibility statement for the order of a stabiliser, via [`CerednikDrinfeld.Omega.exists_int_neighbours_sum_eq_zero_v_apply_smul_eq`](thm.html#CerednikDrinfeld.Omega.exists_int_neighbours_sum_eq_zero_v_apply_smul_eq) and [`CerednikDrinfeld.Omega.natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq`](thm.html#CerednikDrinfeld.Omega.natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Omega.v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (F : K → K) (c₀ c₀' : Γ₀) (m m' : K₀ → ℤ)
    (hstar : ∀ z : K, (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v (z - algebraMap K₀ K t)) →
      Valued.v z < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
        Valued.v (F z) = c₀ * ∏ t ∈ T, Valued.v (z - algebraMap K₀ K t) ^ (m t))
    (hstar' : ∀ w : K, (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v (w - algebraMap K₀ K t)) →
      Valued.v w < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
        Valued.v (F (w * (algebraMap K₀ K ϖ.ϖ)⁻¹)) = c₀' * ∏ t ∈ T, Valued.v (w - algebraMap K₀ K t) ^ (m' t))
    (w w' : K) (hw : w ∈ affinoid ϖ 0) (hw' : w' ∈ affinoid ϖ 0) :
    Valued.v (F (w * (algebraMap K₀ K ϖ.ϖ)⁻¹)) =
      Valued.v (F w') * Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (-(∑ t ∈ T, m t)) := by sorry
