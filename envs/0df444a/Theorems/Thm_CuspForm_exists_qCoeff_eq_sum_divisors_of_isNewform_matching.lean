-- Prove2me | Theorems.Thm_CuspForm_exists_qCoeff_eq_sum_divisors_of_isNewform_matching
-- name    : CuspForm.exists_qCoeff_eq_sum_divisors_of_isNewform_matching
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/3cf31d3b-b655-51ea-a6c6-745e16013a16
-- title:
--   Oldspace expansion of an eigenform matching a newform
-- statement:
--   Let $M$ and $N$ be natural numbers with $N \neq 0$ and $M \mid N$. Let $f_0$ be a weight $2$ cusp form on $\Gamma_0(M)$ which is a newform in the sense of the project: $f_0$ is a normalized eigenform, meaning that its $q$-expansion coefficients $a_n(f_0) =$ `qCoeff f₀ n` (coefficients of the $q$-expansion of period $1$) satisfy $a_1(f_0) = 1$, $a_{mn}(f_0) = a_m(f_0)a_n(f_0)$ for coprime $m, n$, $a_{p^{r+2}}(f_0) = a_p(f_0) a_{p^{r+1}}(f_0) - p\, a_{p^{r}}(f_0)$ for primes $p \nmid M$ and $a_{p^{r+2}}(f_0) = a_p(f_0)a_{p^{r+1}}(f_0)$ for primes $p \mid M$; and moreover for every proper divisor $M'$ of $M$ there is no normalized eigenform of weight $2$ on $\Gamma_0(M')$ whose coefficient at every prime $\ell \nmid M$ agrees with $a_\ell(f_0)$. Let $g$ be a weight $2$ cusp form on $\Gamma_0(N)$ which is a normalized eigenform in the same sense (with $N$ in place of $M$ in the two prime-power recursions), and assume $a_\ell(f_0) = a_\ell(g)$ for every prime $\ell \nmid N$. The conclusion is that there exists a function $c : \mathbb{N} \to \mathbb{C}$ such that for every $n \in \mathbb{N}$ one has $a_n(g) = \sum_{d \mid N/M} c_d \, a_{n/d}(f_0)$, the sum being over the positive divisors $d$ of $N/M$ and a term with $d \nmid n$ read as $0$.
--
--   This is the Atkin–Lehner–Li multiplicity-one theorem in coefficient form: a normalized eigenform of level $N$ whose eigenvalues at the primes not dividing $N$ are those of a newform $f_0$ of level $M \mid N$ lies in the span of the degeneracy images $\tau \mapsto f_0(d\tau)$, $d \mid N/M$. It is used in the project to identify the newform attached to an eigenform arising from a Hecke eigenspace in a Tate module, in particular by [`CuspForm.IsNewform.heckeU_smul_of_mem_heckeEigenspace_tateModule_jZero`](thm.html#CuspForm.IsNewform.heckeU_smul_of_mem_heckeEigenspace_tateModule_jZero), [`CuspForm.exists_isNewform_of_point_of_isUnit_up`](thm.html#CuspForm.exists_isNewform_of_point_of_isUnit_up) and [`CuspForm.exists_isNewform_of_point_of_up_dvd`](thm.html#CuspForm.exists_isNewform_of_point_of_up_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_qCoeff_eq_sum_divisors_of_isNewform_matching.lean

import Definitions.Def_CuspForm_Newforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_qCoeff_eq_sum_divisors_of_isNewform_matching
    (M N : ℕ) [NeZero N] (hMN : M ∣ N)
    (f₀ : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf₀ : f₀.IsNewform)
    (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hg : g.IsNormalizedEigenform)
    (hmatch : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N →
      ModularFormClass.qCoeff f₀ ℓ = ModularFormClass.qCoeff g ℓ) :
    ∃ c : ℕ → ℂ, ∀ n : ℕ, ModularFormClass.qCoeff g n =
      ∑ d ∈ (N / M).divisors, c d * (if d ∣ n then ModularFormClass.qCoeff f₀ (n / d) else 0) := by sorry
