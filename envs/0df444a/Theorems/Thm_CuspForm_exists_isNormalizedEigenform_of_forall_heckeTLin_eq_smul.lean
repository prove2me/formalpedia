-- Prove2me | Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul
-- name    : CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/cf6dd766-4c03-5b6a-a5ee-435a262f90d8
-- title:
--   Realising a partial Hecke eigensystem by a normalised eigenform
-- statement:
--   Let $N$ be a nonzero natural number, let $g$ be a cusp form of weight $2$ for $\Gamma_0(N)$ with $g \neq 0$, let $a : \mathbb{N} \to \mathbb{C}$ be an arbitrary function and let $S \subseteq \mathbb{N}$ be an arbitrary set. Assume that for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S$ one has $\mathrm{heckeTLin}\,2\,g = a(\ell)\cdot g$, where [`CuspForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L69) is the $\mathbb{C}$-linear endomorphism of $S_2(\Gamma_0(N))$ induced by $f \mapsto \mathrm{heckeU}\,k\,\ell\,f + f \mid_k \mathrm{heckeDiagMatrix}\,\ell$. Then there exists a cusp form $h$ of weight $2$ for $\Gamma_0(N)$ which is a normalised eigenform in the coefficient sense of [`CuspForm.IsNormalizedEigenform`](def/FLTPrelim_Modularity.html#L28): writing $c_n(h)$ for the $n$-th coefficient of the $q$-expansion of $h$ with period $1$, one has $c_1(h) = 1$, $c_{mn}(h) = c_m(h)c_n(h)$ for coprime $m, n$, $c_{p^{r+2}}(h) = c_p(h)c_{p^{r+1}}(h) - p\,c_{p^r}(h)$ for every prime $p \nmid N$ and every $r$, and $c_{p^{r+2}}(h) = c_p(h)c_{p^{r+1}}(h)$ for every prime $p \mid N$ and every $r$; moreover $c_\ell(h) = a(\ell)$ for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S$. No relation between $h$ and $g$ beyond this agreement of coefficients is asserted.
--
--   This is the eigensystem-realisation step of the newform layer: a system of Hecke eigenvalues occurring on some nonzero vector of $S_2(\Gamma_0(N))$, known only away from $N$ and away from an arbitrary exceptional set $S$, is realised by a genuine normalised Hecke eigenform of level $N$. It is used in the study of newforms of level $N$, for instance in uniqueness statements for newforms with prescribed coefficients and in the construction of eigenforms attached to lifted or twisted eigensystems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul {N : ℕ} [NeZero N]
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g ≠ 0) (a : ℕ → ℂ) (S : Set ℕ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN g = a ℓ • g) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma0 N) 2, h.IsNormalizedEigenform ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ModularFormClass.qCoeff h ℓ = a ℓ := by sorry
