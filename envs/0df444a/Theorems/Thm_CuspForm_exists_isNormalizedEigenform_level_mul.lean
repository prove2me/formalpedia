-- Prove2me | Theorems.Thm_CuspForm_exists_isNormalizedEigenform_level_mul
-- name    : CuspForm.exists_isNormalizedEigenform_level_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/ee15011a-a87c-5f4b-b325-f7ef858662b5
-- title:
--   p-stabilisation of a normalised eigenform to level Mp
-- statement:
--   Let $M$ be a nonzero natural number and let $f$ be a cusp form of weight $2$ for $\Gamma_0(M)$ which is a normalised eigenform in the coefficient-theoretic sense of the project: writing $a_n =$ `qCoeff f n` for the $n$-th coefficient of the $q$-expansion of $f$ of period $1$, one has $a_1 = 1$, $a_{mn} = a_m a_n$ whenever $m$ and $n$ are coprime, $a_{\ell^{r+2}} = a_\ell a_{\ell^{r+1}} - \ell\, a_{\ell^{r}}$ for every prime $\ell \nmid M$ and every $r$, and $a_{\ell^{r+2}} = a_\ell a_{\ell^{r+1}}$ for every prime $\ell \mid M$ and every $r$. Let $p$ be a prime. The assertion is that there exists a cusp form $g$ of weight $2$ for $\Gamma_0(Mp)$ which is again a normalised eigenform in this sense, now with the two power recursions taken relative to the level $Mp$ (so the three-term recursion is imposed for primes $\ell \nmid Mp$ and the two-term one for primes $\ell \mid Mp$), and such that `qCoeff g n = qCoeff f n` for every $n$ with $p \nmid n$. No claim is made about the coefficients of $g$ at indices divisible by $p$, nor about any Hecke operator acting on $g$.
--
--   This is the $p$-stabilisation of an oldform: it shows that the coefficient-defined predicate of being a normalised eigenform of weight $2$ propagates from level $M$ to level $Mp$ without changing the coefficients away from $p$. It is the one-prime step used by [`CuspForm.exists_isNormalizedEigenform_of_dvd`](thm.html#CuspForm.exists_isNormalizedEigenform_of_dvd), which raises the level along an arbitrary divisibility.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isNormalizedEigenform_level_mul.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_isNormalizedEigenform_level_mul {M : ℕ} [NeZero M]
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f.IsNormalizedEigenform)
    {p : ℕ} (hp : p.Prime) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 (M * p)) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff g n = ModularFormClass.qCoeff f n := by sorry
