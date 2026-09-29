-- Prove2me | Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_dvd
-- name    : CuspForm.exists_isNormalizedEigenform_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/5900691c-707d-51e7-bc49-7bb9c3c2fdba
-- title:
--   Normalised eigenforms ascend from level M to any multiple N
-- statement:
--   Let $M$ and $N$ be natural numbers with $N \neq 0$ and $M \mid N$, and let $f$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(M)$. Write $a_n(h) =$ [`ModularFormClass.qCoeff h n`](def/FLTPrelim_Modularity.html#L19) for the $n$-th coefficient of the $q$-expansion of $h$ taken with width $1$. Assume $f$ satisfies the predicate `IsNormalizedEigenform` at level $M$, that is: $a_1(f) = 1$; $a_{mn}(f) = a_m(f)a_n(f)$ whenever $m$ and $n$ are coprime; for every prime $p \nmid M$ and every $r$, $a_{p^{r+2}}(f) = a_p(f)a_{p^{r+1}}(f) - p\,a_{p^r}(f)$; and for every prime $p \mid M$ and every $r$, $a_{p^{r+2}}(f) = a_p(f)a_{p^{r+1}}(f)$. The conclusion asserts the existence of a cusp form $g$ of weight $2$ for $\Gamma_0(N)$ which satisfies the same four conditions with the level $N$ in place of $M$ (so the prime-power recursions are now split according to divisibility by $N$), and whose coefficients agree with those of $f$ at every index coprime to $N$: $a_n(g) = a_n(f)$ for all $n$ with $\gcd(n,N) = 1$. Only the coefficient conditions are asserted; no Hecke-operator eigenvalue property is mentioned.
--
--   This is the ascent of a normalised eigenform along the divisibility $M \mid N$, classically effected by the degeneracy maps, which preserve the Hecke eigenvalues away from the level. It is used to transport modularity statements phrased through eigenform coefficients at indices coprime to the level from level $M$ to any multiple, by [`WeierstrassCurve.isModularModelOfLevel_of_dvd`](thm.html#WeierstrassCurve.isModularModelOfLevel_of_dvd) and by the statements on residual modularity at a given level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isNormalizedEigenform_of_dvd.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_isNormalizedEigenform_of_dvd {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f.IsNormalizedEigenform) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, n.Coprime N → ModularFormClass.qCoeff g n = ModularFormClass.qCoeff f n := by sorry
