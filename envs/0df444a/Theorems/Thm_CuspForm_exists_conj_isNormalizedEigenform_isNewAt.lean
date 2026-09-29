-- Prove2me | Theorems.Thm_CuspForm_exists_conj_isNormalizedEigenform_isNewAt
-- name    : CuspForm.exists_conj_isNormalizedEigenform_isNewAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/e8c2f315-ce6d-5e5a-90f3-c1c0f5433f93
-- title:
--   Automorphism conjugates of weight-2 normalised eigenforms on Γ₀(M)
-- statement:
--   Let $M$ be a natural number, assumed nonzero, let $\sigma$ be a ring automorphism of $\mathbb{C}$, and let $g$ be a cusp form of weight $2$ for $\Gamma_0(M)$. Write $a_n(f)$ for [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19), the $n$-th coefficient of the $q$-expansion of $f$ taken with respect to the period $1$. Assume $g$ satisfies the coefficient-level eigenform conditions packaged in [`CuspForm.IsNormalizedEigenform`](def/FLTPrelim_Modularity.html#L28): $a_1(g)=1$; $a_{mn}(g)=a_m(g)a_n(g)$ whenever $m$ and $n$ are coprime; for every prime $p$ not dividing $M$ and every $r$, $a_{p^{r+2}}(g)=a_p(g)a_{p^{r+1}}(g)-p\,a_{p^r}(g)$; and for every prime $p$ dividing $M$ and every $r$, $a_{p^{r+2}}(g)=a_p(g)a_{p^{r+1}}(g)$. Assume further, for a natural number $q'$, that [`CuspForm.IsNewAt g q'`](def/FreyPackage_LevelRaising.html#L14) holds, i.e. $a_{q'}(g)^2=1$. The conclusion is that there exists a cusp form $g'$ of weight $2$ for $\Gamma_0(M)$ which again satisfies these four eigenform identities, again satisfies $a_{q'}(g')^2=1$, and whose coefficients are the $\sigma$-conjugates of those of $g$: $a_n(g')=\sigma(a_n(g))$ for every natural number $n$.
--
--   This is the standard statement that an automorphism of $\mathbb{C}$ acting on Fourier coefficients carries a weight-2 normalised eigenform on $\Gamma_0(M)$ to another one, here with the extra condition $a_{q'}^2=1$ carried along. It is used in the level-raising step, where a form produced over some coefficient field must be replaced by a Galois conjugate with prescribed coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_conj_isNormalizedEigenform_isNewAt.lean

import Definitions.Def_FreyPackage_LevelRaising

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_conj_isNormalizedEigenform_isNewAt (M : ℕ) [NeZero M] (σ : ℂ ≃+* ℂ)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hg : CuspForm.IsNormalizedEigenform g)
    (q' : ℕ) (hnew : CuspForm.IsNewAt g q') :
    ∃ g' : CuspForm (CongruenceSubgroup.Gamma0 M) 2, CuspForm.IsNormalizedEigenform g' ∧
      CuspForm.IsNewAt g' q' ∧
      ∀ n : ℕ, ModularFormClass.qCoeff g' n = σ (ModularFormClass.qCoeff g n) := by sorry
