-- Prove2me | Theorems.Thm_AffinePolicies_LargeGap_lemma_8
-- name    : AffinePolicies.LargeGap.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:09:15.218842+00:00
-- url     : https://prove2.me/theorems/bec558e3-83cb-48bd-a954-9caf7b423a81
-- title:
--   Lemma 8, PDF p. 20 — there is an optimal affine solution with P̂_ij = μ (i ≠ j), P̂_jj = θ, q̂_j = λ
-- statement:
--   Let $m\ge 1$, $\delta\in\mathbb R$, and consider the instance (19). There exists an optimal affine solution $(x,\hat y)$,
--   $$\hat y(b)=\hat Pb+\hat q\qquad(b\in\mathcal U),$$
--   and real numbers $\mu,\theta,\lambda$ such that
--
--   1. $\hat P_{ij}=\mu$ for all $i\ne j$ and $\hat P_{jj}=\theta$ for all $j=1,\dots,m$;
--   2. $\hat q_j=\lambda$ for all $j=1,\dots,m$.
--
--   The lemma reduces the analysis of the best affine policy on this instance to three scalar parameters, which the proof of Theorem 3 then bounds.
--
--   **Formalization Note** The existence of an optimal affine solution (attainment of the minimum) is part of the conclusion, as on the page. The hypothesis $m\ge1$ excludes the empty instance; the threshold (18) is not needed.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Lemma 8, PDF p. 20

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

namespace AffinePolicies.LargeGap

theorem lemma_8 (δ : ℝ) (m : ℕ) (hm0 : 0 < m) :
    ∃ (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) (μ θ lam : ℝ),
      AffinePolicies.Simplex.IsOptimalAff (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) x P q ∧
        (∀ i j, i ≠ j → P i j = μ) ∧ (∀ j, P j j = θ) ∧ (∀ j, q j = lam) := by sorry

end AffinePolicies.LargeGap
