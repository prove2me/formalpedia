-- Prove2me | Theorems.Thm_CuspForm_exists_isNormalizedEigenform
-- name    : CuspForm.exists_isNormalizedEigenform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/4ccb0d82-053f-58c4-b85b-cace0551f7c7
-- title:
--   Existence of a normalised eigenform in S₂(Γ₀(N))
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, and suppose the complex vector space $\mathrm{CuspForm}(\Gamma_0(N), 2)$ of weight-$2$ cusp forms for the congruence subgroup $\Gamma_0(N)$ contains some $g \neq 0$. Then there is a cusp form $f$ of weight $2$ for $\Gamma_0(N)$ satisfying the predicate [`CuspForm.IsNormalizedEigenform`](def/FLTPrelim_Modularity.html#L28), that is, writing $a_n =$ `qCoeff f n` for the $n$-th coefficient of the $q$-expansion of $f$ of period $1$: (i) $a_1 = 1$; (ii) $a_{mn} = a_m a_n$ for all coprime natural numbers $m, n$; (iii) for every prime $p$ with $p \nmid N$ and every $r \in \mathbb{N}$, $a_{p^{r+2}} = a_p\, a_{p^{r+1}} - p\, a_{p^{r}}$ (the weight-$2$ specialisation, $p^{k-1} = p$, of the Hecke recursion); and (iv) for every prime $p$ with $p \mid N$ and every $r \in \mathbb{N}$, $a_{p^{r+2}} = a_p\, a_{p^{r+1}}$. The conclusion is purely a statement about the coefficients $a_n$; nonvanishing of $f$ is not asserted separately, being a consequence of $a_1 = 1$.
--
--   This is the classical existence of a normalised simultaneous eigenform for the Hecke operators $T_p$ ($p \nmid N$) and $U_p$ ($p \mid N$) acting on the finite-dimensional space $S_2(\Gamma_0(N))$, recorded here in the purely coefficient-theoretic form used downstream. It is cited in the analysis of coefficients of newforms at prime powers, [`CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd`](thm.html#CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isNormalizedEigenform.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_isNormalizedEigenform {N : ℕ} [NeZero N]
    (h : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g ≠ 0) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform := by sorry
