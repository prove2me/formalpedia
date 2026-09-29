-- Prove2me | Theorems.Thm_CuspForm_IsNewform_level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
-- name    : CuspForm.IsNewform.level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/f3075eb5-6ec4-5967-b194-ed26d66700ca
-- title:
--   Strong multiplicity one across levels for weight-2 newforms
-- statement:
--   Let $M, R, R'$ be natural numbers with $M \neq 0$, and let $g$ be a weight-$2$ cusp form for $\Gamma_0(R)$ and $g'$ a weight-$2$ cusp form for $\Gamma_0(R')$, both assumed to satisfy [`CuspForm.IsNewform`](def/CuspForm_Newforms.html#L23): each is a normalized eigenform, in the sense that its $q$-expansion coefficients $a_n =$ `qCoeff` (the $n$-th coefficient of the $q$-expansion at width $1$) satisfy $a_1 = 1$, $a_{mn} = a_m a_n$ for coprime $m, n$, the recursion $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^r}$ for primes $p$ not dividing the level and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for primes $p$ dividing the level; and each is new, in the sense that for no proper divisor $M_0$ of its level does there exist a normalized eigenform of weight $2$ and level $M_0$ whose coefficients at all primes not dividing the level agree with those of the form. Assume $R \mid M$ and $R' \mid M$, and that $a_\ell(g) = a_\ell(g')$ for every prime $\ell$ not dividing $M$. Then $R = R'$ and $a_n(g) = a_n(g')$ for every natural number $n$, including the indices divisible by primes dividing $M$.
--
--   This is the strong multiplicity one theorem for newforms of weight $2$ on $\Gamma_0$, in the form that agreement of the Hecke eigenvalues away from a common multiple $M$ of the two levels forces the levels and the whole $q$-expansions to coincide. It is used in the project where a newform attached to an elliptic curve or to a Hecke eigensystem must be identified with a given one, for instance in the computations of eigenspaces for Hecke operators and of the Hecke action on Tate modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_level_eq_and_qCoeff_eq_of_forall_qCoeff_eq.lean

import Definitions.Def_CuspForm_Newforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.IsNewform.level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
    {M R R' : ℕ} [NeZero M]
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    {g' : CuspForm (CongruenceSubgroup.Gamma0 R') 2}
    (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g')
    (hR : R ∣ M) (hR' : R' ∣ M)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ) :
    R = R' ∧ ∀ n : ℕ, ModularFormClass.qCoeff g n = ModularFormClass.qCoeff g' n := by sorry
