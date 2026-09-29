-- Prove2me | Theorems.Thm_CongruenceSubgroup_gamma1_inf_gamma0_eq_gamma1_inf_gamma0_mul_of_coprime
-- name    : CongruenceSubgroup.gamma1_inf_gamma0_eq_gamma1_inf_gamma0_mul_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/75bd2b5e-5f7a-51b1-8eb7-d92d9e2d7204
-- title:
--   Γ₁(N)∩Γ₀(ℓ)=Γ₁(N)∩Γ₀(Nℓ) for coprime levels
-- statement:
--   Let $N$ and $\ell$ be natural numbers with $N$ nonzero (as a `NeZero` instance) and $\gcd(N,\ell)=1$. Inside $\mathrm{SL}_2(\mathbb{Z})$, with the Mathlib congruence subgroups $\mathrm{Gamma1}$ and $\mathrm{Gamma0}$ — so that $A \in \Gamma_1(M)$ means that the images of $A_{00}$ and $A_{11}$ in $\mathbb{Z}/M$ are $1$ and the image of $A_{10}$ is $0$, while $A \in \Gamma_0(M)$ means only that the image of $A_{10}$ in $\mathbb{Z}/M$ is $0$ — the assertion is the equality of subgroups $$\Gamma_1(N) \cap \Gamma_0(\ell) \;=\; \Gamma_1(N) \cap \Gamma_0(N\ell),$$ the intersections being taken as meets in the lattice of subgroups of $\mathrm{SL}_2(\mathbb{Z})$. The case $\ell = 0$ is permitted and is then an equality of the same two sides, since $N\cdot 0 = 0$; note that coprimality forces $N = 1$ in that case.
--
--   This is the standard level-bookkeeping identity for congruence subgroups: for $\ell$ coprime to $N$, imposing $\ell \mid c$ on top of $\Gamma_1(N)$ is the same as imposing $N\ell \mid c$. It is used to present the group occurring in the Hecke correspondence of index $\ell$ on $X_1(N)$ as a group of level $N\ell$, and is cited in the identification [`ModularCurve.x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker`](thm.html#ModularCurve.x1x0FunctionFieldC_eq_xHFunctionFieldC_unitsMap_ker) of the corresponding function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CongruenceSubgroup_gamma1_inf_gamma0_eq_gamma1_inf_gamma0_mul_of_coprime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.gamma1_inf_gamma0_eq_gamma1_inf_gamma0_mul_of_coprime (N ℓ : ℕ) [NeZero N]
    (hNℓ : Nat.Coprime N ℓ) :
    CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 ℓ =
      CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 (N * ℓ) := by sorry
