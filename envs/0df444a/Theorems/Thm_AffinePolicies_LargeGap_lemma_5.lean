-- Prove2me | Theorems.Thm_AffinePolicies_LargeGap_lemma_5
-- name    : AffinePolicies.LargeGap.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:08:48.254557+00:00
-- url     : https://prove2.me/theorems/e38a7ff4-4bdb-4618-91b1-65fc0269c985
-- title:
--   Lemma 5, PDF p. 18 — the uncertainty set 𝒰 of (19) is permutation-invariant
-- statement:
--   Let $m\in\mathbb N$ and $\delta\in\mathbb R$, and let $\mathcal U\subseteq\mathbb R^m$ be the uncertainty set of the instance (19): the convex hull of $0$, the unit vectors $e_1,\dots,e_m$, the vector $e/\sqrt m$, and all vectors $\theta_0\mathbf 1_S$ with $|S|=r$. Then for every permutation $\sigma$ of $\{1,\dots,m\}$ and every $b\in\mathbb R^m$,
--   $$b\in\mathcal U\iff b^\sigma\in\mathcal U,\qquad b^\sigma=(b_{\sigma(1)},\dots,b_{\sigma(m)}),$$
--   that is, $\mathcal U$ is permutation-invariant with respect to every $\sigma\in S^m$ (Definition 2).
--
--   This symmetry is what allows an optimal affine policy to be averaged over all permutations (Lemmas 6–8).
--
--   **Formalization Note** The statement holds for every $m$ and $\delta$, so the threshold (18) is not assumed.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Lemma 5, PDF p. 18

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

namespace AffinePolicies.LargeGap

theorem lemma_5 (δ : ℝ) (m : ℕ) :
    ∀ σ : Equiv.Perm (Fin m), AffinePolicies.TwoGap.IsPermInvariant (U19 m δ) σ := by sorry

end AffinePolicies.LargeGap
