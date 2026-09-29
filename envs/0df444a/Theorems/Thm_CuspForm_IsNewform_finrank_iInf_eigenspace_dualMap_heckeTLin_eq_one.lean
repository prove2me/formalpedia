-- Prove2me | Theorems.Thm_CuspForm_IsNewform_finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one
-- name    : CuspForm.IsNewform.finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/9c8858b6-d347-5c95-9d80-a6d0c3c691d5
-- title:
--   Dual multiplicity one for newforms away from finitely many primes
-- statement:
--   Let $M$ be a nonzero natural number and let $g \in S_2(\Gamma_0(M))$ be a weight-two cusp form on $\Gamma_0(M)$ which is a newform in the sense of the project: $g$ is a normalized eigenform, meaning that its $q$-expansion coefficients $a_n(g) = \mathrm{qCoeff}\, g\, n$ (the $n$-th coefficient of the $q$-expansion of $g$ at width $1$) satisfy $a_1(g)=1$, $a_{mn}(g)=a_m(g)a_n(g)$ for coprime $m,n$, $a_{p^{r+2}}(g)=a_p(g)a_{p^{r+1}}(g)-p\,a_{p^r}(g)$ for primes $p \nmid M$ and $a_{p^{r+2}}(g)=a_p(g)a_{p^{r+1}}(g)$ for primes $p \mid M$; and, for every proper divisor $R \mid M$, $R \neq M$, there is no normalized eigenform $h \in S_2(\Gamma_0(R))$ with $a_\ell(h)=a_\ell(g)$ for all primes $\ell \nmid M$. Let $S$ be a finite set of natural numbers. Consider, inside the $\mathbb{C}$-linear dual of $S_2(\Gamma_0(M))$, the intersection over all primes $\ell$ with $\ell \nmid M$ and $\ell \notin S$ of the eigenspaces of the transpose of the Hecke operator [`CuspForm.heckeTLin 2`](def/ModularForm_HeckeOperatorForms.html#L69) at $\ell$ (itself given by $f \mapsto U_\ell f + f \mid_2 \mathrm{diag}$) for the eigenvalue $a_\ell(g)$. The assertion is that this intersection has $\mathbb{C}$-dimension exactly $1$.
--
--   This is the dual (transposed) form of strong multiplicity one for newforms on $\Gamma_0(M)$, with the eigenvalue conditions imposed only at the primes outside $M$ and outside a prescribed finite exceptional set. It is used to pin down eigenforms from their eigensystems away from finitely many primes, and in particular to produce the two-dimensional Hecke eigenspace in the Tate module attached to a newform and to identify the action of the $U_p$ operators on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one.lean

import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.IsNewform.finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (S : Finset ℕ) :
    Module.finrank ℂ ↥(⨅ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S},
        Module.End.eigenspace (CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1).dualMap
          (ModularFormClass.qCoeff g ℓ)) = 1 := by sorry
