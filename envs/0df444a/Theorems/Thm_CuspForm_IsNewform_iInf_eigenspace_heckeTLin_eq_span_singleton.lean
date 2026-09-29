-- Prove2me | Theorems.Thm_CuspForm_IsNewform_iInf_eigenspace_heckeTLin_eq_span_singleton
-- name    : CuspForm.IsNewform.iInf_eigenspace_heckeTLin_eq_span_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/19c5a780-43c2-5e2b-be45-d50a100cdad7
-- title:
--   Multiplicity one: the Hecke eigenspace of a newform is its line
-- statement:
--   Let $M$ be a non-zero natural number and let $g$ be a cusp form of weight $2$ on $\Gamma_0(M)$ which is a newform in the project's sense: that is, $g$ is a normalized eigenform, meaning its $q$-expansion coefficients $a_n(g)$ (the coefficients of the level-one $q$-expansion, written [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19)) satisfy $a_1(g)=1$, $a_{mn}(g)=a_m(g)a_n(g)$ for coprime $m,n$, $a_{p^{r+2}}(g)=a_p(g)a_{p^{r+1}}(g)-p\,a_{p^r}(g)$ for primes $p\nmid M$ and $a_{p^{r+2}}(g)=a_p(g)a_{p^{r+1}}(g)$ for primes $p\mid M$; and, in addition, for no proper divisor $R\mid M$, $R\neq M$, does there exist a normalized eigenform of weight $2$ on $\Gamma_0(R)$ whose coefficients at all primes $\ell\nmid M$ agree with those of $g$. Let $S$ be a finite set of natural numbers. Then the intersection, over all primes $\ell$ with $\ell\nmid M$ and $\ell\notin S$, of the eigenspaces of the Hecke operator $T_\ell$ on weight-two cusp forms of level $M$ (the operator [`CuspForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L69), given by $\ell$-dilation plus the $U_\ell$-type average) for the eigenvalue $a_\ell(g)$, is exactly the complex line $\mathbb{C}\cdot g$. In particular the excluded finite set $S$ of primes does not enlarge the eigenspace.
--
--   This is the multiplicity one theorem of Atkin–Lehner for weight-two newforms, in its eigenvector form and strengthened to allow an arbitrary finite set of primes to be discarded from the collection of Hecke operators used. It serves to identify any character of the level-$M$ Hecke algebra agreeing with $g$ at the operators $T_\ell$ for $\ell$ outside $S$ with the full eigencharacter of $g$, and is used in the comparison of a Frey-package eigenform with the lattice-theoretic data attached to it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_iInf_eigenspace_heckeTLin_eq_span_singleton.lean

import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.IsNewform.iInf_eigenspace_heckeTLin_eq_span_singleton
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (S : Finset ℕ) :
    (⨅ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S},
        Module.End.eigenspace (CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1)
          (ModularFormClass.qCoeff g ℓ)) = ℂ ∙ g := by sorry
