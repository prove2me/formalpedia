-- Prove2me | Theorems.Thm_CongruenceSubgroup_eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq
-- name    : CongruenceSubgroup.eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/7f7c71ea-e040-56c3-a693-c3f8106ba88b
-- title:
--   Elements of ±Γ₁(M), M ≥ 4, fixing a point of H
-- statement:
--   Let $M$ be a natural number with $4 \le M$, and let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ be such that either $\gamma$ or $-\gamma$ lies in the congruence subgroup $\Gamma_1(M)$ (in Mathlib's formulation, `CongruenceSubgroup.Gamma1 M`, whose membership condition is that the $(0,0)$ and $(1,1)$ entries reduce to $1$ in $\mathbb{Z}/M$ and the $(1,0)$ entry reduces to $0$). Suppose there is a point $\tau$ of the upper half plane $\mathfrak{H}$ fixed by $\gamma$ for the usual action of $\mathrm{SL}_2(\mathbb{Z})$ on $\mathfrak{H}$ by fractional linear transformations, i.e. $\gamma \cdot \tau = \tau$. Then $\gamma = 1$ or $\gamma = -1$ in $\mathrm{SL}_2(\mathbb{Z})$. Thus the group $\pm\Gamma_1(M)$ acts on $\mathfrak{H}$ with trivial stabilisers modulo $\pm 1$ once $M \ge 4$.
--
--   This is the group-theoretic statement that $\Gamma_1(M)$ has no elliptic elements for $M \ge 4$, so that the modular curve $X_1(M)$ has no elliptic points (Diamond–Shurman, Exercise 2.3.7). It is used in the computation of genera and orders of vanishing on modular curves of level $\Gamma_1(M)$, specifically by [`ModularCurve.FullLevel.genusFF_fieldBar_eq`](thm.html#ModularCurve.FullLevel.genusFF_fieldBar_eq) and by [`ModularCurve.ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure`](thm.html#ModularCurve.ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CongruenceSubgroup_eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.eq_one_or_eq_neg_one_of_mem_Gamma1_of_smul_eq (M : ℕ) (hM : 4 ≤ M)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 M ∨ -γ ∈ CongruenceSubgroup.Gamma1 M)
    (τ : UpperHalfPlane) (hτ : γ • τ = τ) : γ = 1 ∨ γ = -1 := by sorry
