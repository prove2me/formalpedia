-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root
-- name    : CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/0a80d253-c903-5dd1-bf9e-2a8a417fbe13
-- title:
--   Oldforms of level N with prescribed coefficients at bad primes
-- statement:
--   Let $M$ and $N$ be nonzero natural numbers with $M \mid N$, and let $f$ be a weight-two cusp form on $\Gamma_0(M)$ which is a normalised eigenform in the $q$-expansion sense recorded by the project predicate: writing $a_n(f)$ for the $n$-th coefficient of the $q$-expansion of $f$ at width $1$, one has $a_1(f)=1$, $a_{mn}(f)=a_m(f)a_n(f)$ for coprime $m,n$, $a_{p^{r+2}}(f)=a_p(f)a_{p^{r+1}}(f)-p\,a_{p^r}(f)$ for primes $p\nmid M$, and $a_{p^{r+2}}(f)=a_p(f)a_{p^{r+1}}(f)$ for primes $p\mid M$. Let $\alpha:\mathbb{N}\to\mathbb{C}$ be any function such that for every prime $q$ with $q\mid N$, $q\nmid M$ and $q^2\nmid N$ the value $\alpha(q)$ is a root of the Hecke polynomial $X^2-a_q(f)X+q$. Then there exists a weight-two cusp form $g$ on $\Gamma_0(N)$, again a normalised eigenform in the above sense, whose coefficients at primes are: $a_\ell(g)=a_\ell(f)$ for every prime $\ell\nmid N$; $a_q(g)=a_q(f)$ for every prime $q\mid N$ with equal $q$-adic valuations of $N$ and $M$; $a_q(g)=\alpha(q)$ for every prime $q\mid N$ with $q\nmid M$ and $q^2\nmid N$; and $a_q(g)=0$ for every prime $q$ with $q^2\mid N$ and $v_q(M)<v_q(N)$.
--
--   This is the passage from an eigenform of level $M$ to the associated oldforms of level $N$, with prescribed eigenvalues at the primes of $N/M$: $q$-stabilisation at the primes dividing $N$ exactly once and not dividing $M$, and $q$-depletion (eigenvalue $0$) at the remaining primes of $N/M$, as in the theory of Atkin–Lehner and Li. It is used in the study of the Hecke algebra at the primes of bad reduction, in particular to extend ring homomorphisms of Hecke algebras to ones sending $U_q$ to $0$, and in the comparison of the $T_q$- and $U_q$-actions when $q^2 \mid N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f.IsNormalizedEigenform)
    (α : ℕ → ℂ)
    (hα : ∀ q : ℕ, q.Prime → q ∣ N → ¬ q ∣ M → ¬ q ^ 2 ∣ N →
      α q ^ 2 - ModularFormClass.qCoeff f q * α q + q = 0) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g.IsNormalizedEigenform ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff f ℓ) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → N.factorization q = M.factorization q →
        ModularFormClass.qCoeff g q = ModularFormClass.qCoeff f q) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → ¬ q ∣ M → ¬ q ^ 2 ∣ N →
        ModularFormClass.qCoeff g q = α q) ∧
      (∀ q : ℕ, q.Prime → q ^ 2 ∣ N → M.factorization q < N.factorization q →
        ModularFormClass.qCoeff g q = 0) := by sorry
