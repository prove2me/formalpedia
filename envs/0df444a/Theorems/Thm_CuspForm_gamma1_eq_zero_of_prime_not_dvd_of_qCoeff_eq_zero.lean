-- Prove2me | Theorems.Thm_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
-- name    : CuspForm.gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/8fee0354-f6d6-5b66-8ce1-40999d05f4a9
-- title:
--   Vanishing of cusp forms supported on multiples of p
-- statement:
--   Let $N$ be a positive integer, $p$ a prime not dividing $N$, and $k$ an integer. Let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_1(N)$ (viewed, via the usual coercion, as a subgroup of $\mathrm{GL}_2(\mathbb{R})$ acting on the upper half-plane). Assume that for every natural number $n$ with $p \nmid n$ the $n$-th coefficient of the $q$-expansion of $f$ of width $1$ vanishes, i.e. $\mathrm{qCoeff}\,f\,n$, defined as the $n$-th coefficient of the power series $\mathrm{qExpansion}\,1\,f$ attached to the underlying function $\mathbb{H} \to \mathbb{C}$, is $0$; in the usual notation $f = \sum_{n \ge 0} a_n q^n$ with $q = e^{2\pi i \tau}$, the hypothesis is $a_n = 0$ for all $n$ prime to $p$ (the index $n = 0$ is not constrained by the hypothesis, since $p \mid 0$). The conclusion is that $f$ is the zero cusp form.
--
--   This is the Atkin–Lehner vanishing lemma underlying the theory of newforms: a nonzero cusp form on $\Gamma_1(N)$ cannot have its Fourier expansion supported on the multiples of a prime $p \nmid N$, equivalently cannot be of the shape $g(p\tau)$. The proof reduces to [`CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1`](thm.html#CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1), which kills cusp forms whose slash by $\mathrm{diag}(p,1)$ is again invariant under $\Gamma_1(N)$; the present statement is in turn used by [`CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero`](thm.html#CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
    {N p : ℕ} [NeZero N] (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) : f = 0 := by sorry
