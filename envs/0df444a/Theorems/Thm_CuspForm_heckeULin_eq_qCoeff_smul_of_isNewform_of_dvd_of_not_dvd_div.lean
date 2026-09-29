-- Prove2me | Theorems.Thm_CuspForm_heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div
-- name    : CuspForm.heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/5462fe5e-7797-584c-bdcf-9abcc3c59fa8
-- title:
--   U_q acts by a_q(g) on the g-eigenpacket
-- statement:
--   Let $M \mid N$ be nonzero natural numbers, let $S$ be a finite set of natural numbers, and let $g$ be a weight-$2$ cusp form on $\Gamma_0(M)$ that is a newform in the sense used here: $g$ is a normalised eigenform (its $q$-expansion coefficients, taken with respect to period $1$, satisfy $a_1(g)=1$, $a_{mn}(g)=a_m(g)a_n(g)$ for coprime $m,n$, the recursion $a_{p^{r+2}}(g)=a_p(g)a_{p^{r+1}}(g)-p\,a_{p^r}(g)$ for primes $p \nmid M$ and $a_{p^{r+2}}(g)=a_p(g)a_{p^{r+1}}(g)$ for primes $p \mid M$), and moreover for no proper divisor $R$ of $M$ does there exist a normalised eigenform of weight $2$ on $\Gamma_0(R)$ whose coefficients at all primes $\ell \nmid M$ agree with those of $g$. Let $q$ be a prime with $q \mid M$ and $q \nmid N/M$, and let $f$ be a weight-$2$ cusp form on $\Gamma_0(N)$ such that for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S$ one has $T_\ell f = a_\ell(g)\, f$, where $T_\ell$ is the level-$N$ operator [`CuspForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L69) in weight $2$. Then the level-$N$ operator $U_q$ ([`CuspForm.heckeULin`](def/ModularForm_HeckeOperatorForms.html#L83) in weight $2$, formed from the divisibility $q \mid M \mid N$) satisfies $U_q f = a_q(g)\, f$.
--
--   This is the Atkin–Lehner–Li statement that on the space of forms of level $N$ whose $T_\ell$-eigenvalues away from $N$ and outside a finite exceptional set are those of a newform $g$ of level $M$, the operator $U_q$ at a prime $q$ dividing $M$ but not $N/M$ acts by the scalar $a_q(g)$. It is used in the analysis of the local behaviour of the Hecke algebra at primes where the relevant representation is not unramified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div.lean

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularFormClass

theorem CuspForm.heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div
    (N M : ℕ) [NeZero N] [NeZero M] (hMN : M ∣ N) (S : Finset ℕ)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hg : g.IsNewform)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqNM : ¬ q ∣ N / M)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hf : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN f = qCoeff g ℓ • f) :
    CuspForm.heckeULin 2 (hqM.trans hMN) f = qCoeff g q • f := by sorry
