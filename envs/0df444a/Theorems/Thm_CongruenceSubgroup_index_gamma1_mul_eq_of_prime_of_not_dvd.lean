-- Prove2me | Theorems.Thm_CongruenceSubgroup_index_gamma1_mul_eq_of_prime_of_not_dvd
-- name    : CongruenceSubgroup.index_gamma1_mul_eq_of_prime_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/119445ce-0479-5861-a6c3-8421120cf4ca
-- title:
--   Index of Γ₁(Mp) for p∤ M
-- statement:
--   Let $M$ be a non-zero natural number and let $p$ be a prime, and assume that $p$ does not divide $M$. The assertion is an identity between indices of congruence subgroups of $\mathrm{SL}_2(\mathbb{Z})$, where $\Gamma_1(N)$ denotes, as in Mathlib, the subgroup of matrices in $\mathrm{SL}_2(\mathbb{Z})$ whose reduction modulo $N$ is upper triangular unipotent (first column congruent to $(1,0)$ and lower right entry congruent to $1$ modulo $N$), and the index is the cardinality of the set of cosets in $\mathrm{SL}_2(\mathbb{Z})$, as a natural number. The conclusion is
--   $$[\mathrm{SL}_2(\mathbb{Z}):\Gamma_1(Mp)] = (p^2-1)\,[\mathrm{SL}_2(\mathbb{Z}):\Gamma_1(M)],$$
--   with $p^2-1$ understood as truncated subtraction of natural numbers (harmless here, since $p^2\ge 1$). Equivalently, the relative index $[\Gamma_1(M):\Gamma_1(Mp)]$ equals $p^2-1$. The proof invokes the surjectivity of the reduction map $\mathrm{SL}_2(\mathbb{Z})\to\mathrm{SL}_2(\mathbb{Z}/N)$ on special linear groups, in the form [`ModularCurve.surjective_specialLinearGroup_map_zmod`](thm.html#ModularCurve.surjective_specialLinearGroup_map_zmod).
--
--   This is the standard multiplicativity step in the computation of the index of $\Gamma_1(N)$ in $\mathrm{SL}_2(\mathbb{Z})$, isolating the factor $p^2-1 = \#(\mathbb{F}_p^2\setminus\{0\})$ contributed by a prime $p$ exactly dividing the level. It feeds the combined index and double-coset count [`CongruenceSubgroup.index_gamma1_mul_and_natCard_doubleCoset_gamma1_mul_of_prime_of_not_dvd`](thm.html#CongruenceSubgroup.index_gamma1_mul_and_natCard_doubleCoset_gamma1_mul_of_prime_of_not_dvd) and the computation of the relative degree of the function field of $X_1(Mp)$ over that of $X_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CongruenceSubgroup_index_gamma1_mul_eq_of_prime_of_not_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.index_gamma1_mul_eq_of_prime_of_not_dvd
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) :
    (CongruenceSubgroup.Gamma1 (M * p)).index = (p ^ 2 - 1) * (CongruenceSubgroup.Gamma1 M).index := by sorry
