-- Prove2me | Theorems.Thm_CuspForm_qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform
-- name    : CuspForm.qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/c61f91ca-90f5-540d-8806-79ef2cc19125
-- title:
--   Eigenvalue aₚ² ≠ (1+p)² at primes not dividing the level
-- statement:
--   Let $N_0$ and $p$ be natural numbers with $p$ prime and $p \nmid N_0$, and let $h$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(N_0)$. Write $a_n(h)$ for the $n$-th coefficient [`ModularFormClass.qCoeff h n`](def/FLTPrelim_Modularity.html#L19) of the $q$-expansion of $h$ of width $1$. Assume that $h$ satisfies the predicate [`CuspForm.IsNormalizedEigenform`](def/FLTPrelim_Modularity.html#L28), that is, the four conditions on these coefficients: $a_1(h) = 1$; $a_{mn}(h) = a_m(h)\,a_n(h)$ whenever $m$ and $n$ are coprime; for every prime $\ell$ with $\ell \nmid N_0$ and every $r \ge 0$ the recursion $a_{\ell^{r+2}}(h) = a_\ell(h)\,a_{\ell^{r+1}}(h) - \ell\,a_{\ell^{r}}(h)$; and for every prime $\ell$ dividing $N_0$ and every $r \ge 0$ the recursion $a_{\ell^{r+2}}(h) = a_\ell(h)\,a_{\ell^{r+1}}(h)$. The conclusion is the inequality of complex numbers $a_p(h)^2 \neq (1 + p)^2$, equivalently $a_p(h) \neq 1 + p$ and $a_p(h) \neq -(1+p)$; equivalently again, neither $1$ nor $-1$ is a root of $X^2 - a_p(h)X + p$. No positivity or nonvanishing hypothesis on $N_0$ is imposed.
--
--   This is the fragment of the Ramanujan–Petersson (Hasse–Weil) estimate $|a_p| \le 2\sqrt{p}$ that concerns only the two boundary values $a_p = \pm(1+p)$, obtained here from the Eichler–Shimura congruence relation and the action of Frobenius on the Tate module of $J_0(N_0)$ rather than from the Riemann hypothesis for curves over finite fields. It is used, via [`CuspForm.heckeLocal.unitRoot_sq_ne_one_of_point`](thm.html#CuspForm.heckeLocal.unitRoot_sq_ne_one_of_point), to know that the unit root of the Hecke polynomial $X^2 - a_pX + p$ at a prime of good reduction is not $\pm 1$, which is what makes the level-raising comparison at $p$ nondegenerate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform.lean

import Definitions.Def_CuspForm_Newforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform
    (N₀ p : ℕ) (hp : p.Prime) (hpN₀ : ¬ p ∣ N₀)
    (h : CuspForm (CongruenceSubgroup.Gamma0 N₀) 2) (hh : h.IsNormalizedEigenform) :
    ModularFormClass.qCoeff h p ^ 2 ≠ ((1 : ℂ) + p) ^ 2 := by sorry
