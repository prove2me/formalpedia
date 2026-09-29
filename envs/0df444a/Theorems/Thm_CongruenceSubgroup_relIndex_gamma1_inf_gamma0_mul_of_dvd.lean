-- Prove2me | Theorems.Thm_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd
-- name    : CongruenceSubgroup.relIndex_gamma1_inf_gamma0_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/862019c1-b499-5a93-8ad8-d0c0995cbb35
-- title:
--   Relative index of Γ₁(M)∩Γ₀(Mq) in Γ₁(M)
-- statement:
--   Let $M$ be a natural number with $M \neq 0$ and let $q$ be a natural number dividing $M$. Consider inside $\mathrm{SL}_2(\mathbf{Z})$ the congruence subgroups $\Gamma_1(M)$, consisting of the matrices $\begin{pmatrix} a & b \\ c & d\end{pmatrix}$ with $a \equiv 1$, $d \equiv 1$ and $c \equiv 0 \pmod M$, and $\Gamma_0(Mq)$, consisting of the matrices whose lower-left entry is $\equiv 0 \pmod{Mq}$. The assertion is that the relative index of $\Gamma_1(M) \sqcap \Gamma_0(Mq)$ in $\Gamma_1(M)$ — that is, the index of the subgroup $\Gamma_1(M) \cap \Gamma_0(Mq)$ of $\Gamma_1(M)$, viewed as a subgroup of $\Gamma_1(M)$ — equals $q$, as an equality of natural numbers. No primality assumption on $q$ is made, and the divisibility $q \mid M$ is genuinely used.
--
--   This is the standard index computation for the chain $\Gamma_1(M) \cap \Gamma_0(Mq) \subseteq \Gamma_1(M)$ when $q \mid M$, in the relative-index form convenient for group-theoretic bookkeeping. It feeds the index computation for subgroups sandwiched between $\Gamma_1(M)$ and $\Gamma_0(M)$ together with $-1$, and the computations of ranks of spaces of modular forms along Hecke correspondences on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CongruenceSubgroup.relIndex_gamma1_inf_gamma0_mul_of_dvd (M q : ℕ) [NeZero M] (hq : q ∣ M) :
    (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * q)).relIndex (CongruenceSubgroup.Gamma1 M) = q := by sorry
