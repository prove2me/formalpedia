-- Prove2me | Theorems.Thm_CuspForm_exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
-- name    : CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/5061d16a-b35b-53c8-a8e2-03e6654be7fe
-- title:
--   Atkin–Lehner: coefficients vanishing off K force lower level
-- statement:
--   Let $N$ be a nonzero natural number, $k$ an integer, and $K$ a nonzero natural number, and let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_1(N)$. Write $\mathrm{qCoeff}(h,n)$ for the $n$-th coefficient of the $q$-expansion of width $1$ of a function $h$ on the upper half-plane, so that for $f$ these are its Fourier coefficients $a_n(f)$. Assume that $a_n(f)=0$ for every natural number $n$ with $\gcd(n,K)=1$. The assertion is the existence of a family $g$ assigning to each natural number $p$ a cusp form $g_p$ of weight $k$ for $\Gamma_1(N/p)$ (the natural-number quotient), such that for every natural number $n$
--   $$a_n(f)=\sum_{p \mid N,\ p \text{ prime}} \begin{cases} a_{n/p}(g_p) & p \mid n\\ 0 & \text{otherwise,}\end{cases}$$
--   the sum being over the prime factors of $N$ and $n/p$ the natural-number quotient. Only the values of $g$ at the prime divisors of $N$ enter the conclusion. The conclusion is an identity of Fourier coefficients, i.e. the coefficientwise form of $f(\tau)=\sum_{p\mid N} g_p(p\tau)$, rather than an identity of functions.
--
--   This is the main lemma underlying the theory of newforms, due to Atkin and Lehner (the case $K=N$ is Theorem 5.7.1 of Diamond–Shurman); the formulation with an auxiliary modulus $K$ is what the inductive removal of primes dividing $K$ but not $N$ produces. It is used here as the coefficient-free input to the version that also tracks nebentypus characters, [`CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero`](thm.html#CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero), and its proof cites the vanishing of $a_n(f)$ for $n$ coprime to $N$, the descent of a sum of forms on $\Gamma(N)$ to forms invariant under the groups $\Gamma_1(N/p)$, and the degeneracy maps $g \mapsto g(d\tau)$ on $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
    (N : ℕ) [NeZero N] (k : ℤ) (K : ℕ) (hK : K ≠ 0) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff f n = 0) :
    ∃ g : (p : ℕ) → CuspForm (Gamma1 (N / p)) k,
      ∀ n : ℕ, ModularFormClass.qCoeff f n =
        ∑ p ∈ N.primeFactors, if p ∣ n then ModularFormClass.qCoeff (g p) (n / p) else 0 := by sorry
