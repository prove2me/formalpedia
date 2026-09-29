-- Prove2me | Theorems.Thm_CuspForm_IsNewform_eq_of_forall_qCoeff_eq
-- name    : CuspForm.IsNewform.eq_of_forall_qCoeff_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/28387245-e39b-575c-ab1b-db0842bc607d
-- title:
--   Strong multiplicity one for newforms of a fixed level
-- statement:
--   Let $M$ and $R$ be natural numbers with $M$ nonzero and $R \mid M$, and let $g, g'$ be cusp forms of weight $2$ for $\Gamma_0(R)$, both assumed to be newforms in the sense of the project predicate [`CuspForm.IsNewform`](def/CuspForm_Newforms.html#L23): each is a normalised eigenform, meaning that its $q$-expansion coefficients (taken with respect to the parameter $q$ of width $1$, i.e. [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19)) satisfy $a_1 = 1$, the multiplicativity $a_{mn} = a_m a_n$ for coprime $m, n$, the recursion $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\, a_{p^{r}}$ at primes $p \nmid R$ and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ at primes $p \mid R$; and each has no lower level carrying the same eigensystem, in the sense that for every proper divisor $M_0 \mid R$, $M_0 \neq R$, there is no normalised eigenform of weight $2$ on $\Gamma_0(M_0)$ whose $\ell$-th coefficient agrees with that of the given form for all primes $\ell \nmid R$. Assume further that $a_\ell(g) = a_\ell(g')$ for every prime $\ell$ not dividing $M$. Then $g = g'$.
--
--   This is strong multiplicity one for weight-two newforms of a fixed level, in the form in which the exceptional set of primes is allowed to be any set of divisors of a multiple $M$ of the level rather than just the primes dividing the level itself. It is used to identify newforms from their Hecke eigenvalues away from a finite set of primes, and feeds the two companion results comparing levels and all coefficients of two newforms agreeing at the good primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_eq_of_forall_qCoeff_eq.lean

import Definitions.Def_CuspForm_Newforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.IsNewform.eq_of_forall_qCoeff_eq
    {M R : ℕ} [NeZero M]
    {g g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g')
    (hR : R ∣ M)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ) :
    g = g' := by sorry
