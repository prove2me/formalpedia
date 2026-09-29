-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_stabilization_qCoeff_eq
-- name    : CuspForm.IsNormalizedEigenform.exists_stabilization_qCoeff_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/b57d3826-2124-5086-bef5-768a9e83e38d
-- title:
--   p-stabilisation of a normalised eigenform to level Mp
-- statement:
--   Let $M$ be a nonzero natural number and let $g$ be a weight-two cusp form on $\Gamma_0(M)$ which is a normalised eigenform in the sense of the project's predicate: writing $a_n(g)$ for the $n$-th coefficient of the $q$-expansion of $g$ at width $1$, one has $a_1(g)=1$, $a_{mn}(g)=a_m(g)a_n(g)$ whenever $\gcd(m,n)=1$, and for every prime $q$ and every $r$ the recursions $a_{q^{r+2}}(g)=a_q(g)a_{q^{r+1}}(g)-q\,a_{q^r}(g)$ if $q\nmid M$ and $a_{q^{r+2}}(g)=a_q(g)a_{q^{r+1}}(g)$ if $q\mid M$. Let $p$ be a prime with $p\nmid M$, and let $\varepsilon\in\mathbb{C}$ satisfy $\varepsilon^2-a_p(g)\varepsilon+p=0$. The conclusion asserts the existence of a weight-two cusp form $f$ on $\Gamma_0(Mp)$ which is again a normalised eigenform in the same sense (now with the two prime-power recursions read with respect to the level $Mp$), whose $q$-expansion coefficients satisfy $a_n(f)=a_n(g)$ for every $n$ with $p\nmid n$, and whose $p$-th coefficient is $a_p(f)=\varepsilon$.
--
--   This is the classical $p$-stabilisation of an eigenform of level prime to $p$, which in coefficient terms replaces $g$ by $g(z)-\varepsilon'g(pz)$ for $\varepsilon'$ the complementary root of $X^2-a_p(g)X+p$; no newness of $g$ and no unit condition on $\varepsilon$ are required, and the two roots give two (possibly equal) stabilisations. Within this development it supplies, from a form of level $M$, an eigenform of level $Mp$ with prescribed $p$-th coefficient, and is used in establishing [`CuspForm.point_dichotomy_at_exactly_dvd_of_ne_two`](thm.html#CuspForm.point_dichotomy_at_exactly_dvd_of_ne_two); the underlying effect of the diagonal rescaling $\tau\mapsto p\tau$ on $q$-expansions is recorded in [`ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul`](thm.html#ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_exists_stabilization_qCoeff_eq.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.IsNormalizedEigenform.exists_stabilization_qCoeff_eq
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hg : g.IsNormalizedEigenform) (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
    (ε : ℂ) (hε : ε ^ 2 - ModularFormClass.qCoeff g p * ε + p = 0) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 (M * p)) 2, f.IsNormalizedEigenform ∧
      (∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) ∧
      ModularFormClass.qCoeff f p = ε := by sorry
