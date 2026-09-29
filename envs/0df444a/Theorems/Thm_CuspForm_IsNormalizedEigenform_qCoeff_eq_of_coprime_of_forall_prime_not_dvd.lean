-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd
-- name    : CuspForm.IsNormalizedEigenform.qCoeff_eq_of_coprime_of_forall_prime_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/117da99f-426c-57ea-ab55-4a6a71b2d1c5
-- title:
--   Coefficients at indices coprime to M agree
-- statement:
--   Let $M$, $R$, $R'$ be natural numbers, let $g$ be a weight-$2$ cusp form for $\Gamma_0(R)$ and $g'$ a weight-$2$ cusp form for $\Gamma_0(R')$, and write $\mathrm{qCoeff}\,f\,n$ for the $n$-th coefficient of the $q$-expansion of $f$ at width $1$. Assume that each of $g$ and $g'$ satisfies the predicate [`CuspForm.IsNormalizedEigenform`](def/FLTPrelim_Modularity.html#L28) for its own level $N \in \{R, R'\}$, i.e. its first coefficient equals $1$, its coefficients are multiplicative at coprime pairs of indices, and for every prime $p$ and every $r$ one has $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^r}$ when $p \nmid N$ and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ when $p \mid N$. Assume moreover that $R \mid M$ and $R' \mid M$, and that the coefficients of $g$ and $g'$ agree at every prime $\ell$ with $\ell \nmid M$. Then for every natural number $n$ coprime to $M$ the coefficients agree: $\mathrm{qCoeff}\,g\,n = \mathrm{qCoeff}\,g'\,n$.
--
--   This is the standard passage from agreement of Hecke eigenvalues at the primes outside a fixed modulus to agreement of all Fourier coefficients at indices coprime to that modulus, for normalised eigenforms of weight $2$ on $\Gamma_0$ of levels dividing $M$. It is used in the comparison of newforms: it feeds the identification of two newforms having the same coefficients and the determination of levels from coefficients at good primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.IsNormalizedEigenform.qCoeff_eq_of_coprime_of_forall_prime_not_dvd
    {M R R' : ℕ}
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    {g' : CuspForm (CongruenceSubgroup.Gamma0 R') 2}
    (hg : CuspForm.IsNormalizedEigenform g) (hg' : CuspForm.IsNormalizedEigenform g')
    (hR : R ∣ M) (hR' : R' ∣ M)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ)
    {n : ℕ} (hn : Nat.Coprime n M) :
    ModularFormClass.qCoeff g n = ModularFormClass.qCoeff g' n := by sorry
