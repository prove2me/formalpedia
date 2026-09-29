-- Prove2me | Theorems.Thm_CuspForm_IsNewform_level_eq_of_forall_prime_not_dvd_qCoeff_eq
-- name    : CuspForm.IsNewform.level_eq_of_forall_prime_not_dvd_qCoeff_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/61b9f78f-8acf-55bb-84ac-590f47f1b70d
-- title:
--   Equality of levels for weight-2 newforms with matching eigenvalues
-- statement:
--   Let $M$ be a nonzero natural number and let $R, R'$ be natural numbers dividing $M$. Let $g$ be a weight-$2$ cusp form on $\Gamma_0(R)$ and $g'$ a weight-$2$ cusp form on $\Gamma_0(R')$, and write $\mathrm{qCoeff}(f,n)$ for the $n$-th coefficient of the $q$-expansion of $f$ (of width $1$). Assume that each of $g$ and $g'$ is a newform in the sense of the project's predicate [`CuspForm.IsNewform`](def/CuspForm_Newforms.html#L23): that is, $g$ is a normalised eigenform on $\Gamma_0(R)$ — $\mathrm{qCoeff}(g,1)=1$, the coefficients are multiplicative on coprime indices, and they satisfy the recursions $\mathrm{qCoeff}(g,p^{r+2}) = \mathrm{qCoeff}(g,p)\,\mathrm{qCoeff}(g,p^{r+1}) - p\,\mathrm{qCoeff}(g,p^{r})$ for primes $p \nmid R$ and $\mathrm{qCoeff}(g,p^{r+2}) = \mathrm{qCoeff}(g,p)\,\mathrm{qCoeff}(g,p^{r+1})$ for primes $p \mid R$ — and, for every proper divisor $N$ of $R$, there is no normalised eigenform on $\Gamma_0(N)$ whose coefficients at the primes not dividing $R$ agree with those of $g$; likewise for $g'$ with $R'$ in place of $R$. Assume finally that $\mathrm{qCoeff}(g,\ell) = \mathrm{qCoeff}(g',\ell)$ for every prime $\ell$ not dividing $M$. The conclusion is $R = R'$.
--
--   This is the level half of strong multiplicity one for weight-$2$ newforms: agreement of the eigenvalues at all primes outside a fixed finite set forces the two newforms to have the same level. It is combined with the equal-level uniqueness statement [`CuspForm.IsNewform.eq_of_forall_qCoeff_eq`](thm.html#CuspForm.IsNewform.eq_of_forall_qCoeff_eq) in [`CuspForm.IsNewform.level_eq_and_qCoeff_eq_of_forall_qCoeff_eq`](thm.html#CuspForm.IsNewform.level_eq_and_qCoeff_eq_of_forall_qCoeff_eq), and is used in the decomposition of Hecke eigenvectors in spaces of cusp forms on $\Gamma_0(M)$ into rescalings of newforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_level_eq_of_forall_prime_not_dvd_qCoeff_eq.lean

import Definitions.Def_CuspForm_Newforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.IsNewform.level_eq_of_forall_prime_not_dvd_qCoeff_eq
    {M R R' : ℕ} [NeZero M]
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    {g' : CuspForm (CongruenceSubgroup.Gamma0 R') 2}
    (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g')
    (hR : R ∣ M) (hR' : R' ∣ M)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ) :
    R = R' := by sorry
