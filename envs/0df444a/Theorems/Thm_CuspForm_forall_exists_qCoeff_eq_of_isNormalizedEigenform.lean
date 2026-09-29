-- Prove2me | Theorems.Thm_CuspForm_forall_exists_qCoeff_eq_of_isNormalizedEigenform
-- name    : CuspForm.forall_exists_qCoeff_eq_of_isNormalizedEigenform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/5e9ace83-c673-5cc1-9749-50d35156f01d
-- title:
--   Algebraic integrality of all q-coefficients of a normalised eigenform
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, and let $g$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(N)$. Write $a_n(g)$ for the $n$-th coefficient of the $q$-expansion of $g$ with respect to width $1$, i.e. [`ModularFormClass.qCoeff g n`](def/FLTPrelim_Modularity.html#L19), the coefficient of index $n$ of `qExpansion 1 g`. Assume `g.IsNormalizedEigenform`, which by definition packages four conditions: $a_1(g) = 1$; $a_{mn}(g) = a_m(g)\,a_n(g)$ for all coprime $m, n$; for every prime $p$ with $p \nmid N$ and every $r \ge 0$ the recursion $a_{p^{r+2}}(g) = a_p(g)\,a_{p^{r+1}}(g) - p\,a_{p^{r}}(g)$; and for every prime $p$ with $p \mid N$ and every $r \ge 0$ the recursion $a_{p^{r+2}}(g) = a_p(g)\,a_{p^{r+1}}(g)$. The conclusion is that for every natural number $n$ there exists an element $a$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ whose image in $\mathbb{C}$ equals $a_n(g)$; that is, every $q$-expansion coefficient of $g$ is an algebraic integer.
--
--   This is the standard integrality statement for the Fourier coefficients of a weight-two normalised Hecke eigenform on $\Gamma_0(N)$, here derived purely from the normalisation and the Hecke recursions. It feeds the constructions attaching ring homomorphisms out of the Hecke algebra to such an eigenform, which are used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_forall_exists_qCoeff_eq_of_isNormalizedEigenform.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.forall_exists_qCoeff_eq_of_isNormalizedEigenform {N : ℕ} [NeZero N]
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNormalizedEigenform) :
    ∀ n : ℕ, ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g n := by sorry
