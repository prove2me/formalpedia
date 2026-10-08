-- Prove2me | Theorems.Thm_AffinePolicies_SqrtBound_lemma_9
-- name    : AffinePolicies.SqrtBound.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:40:19.770792+00:00
-- url     : https://prove2.me/theorems/10e4b432-c61c-44f6-b09b-ef9d64f19799
-- title:
--   Lemma 9, PDF p. 28 — after Algorithm 𝒜: Σ_{j∈J₁} b_j/μ_j ≤ √m and b_j ≤ β_j on J₂
-- statement:
--   Let $\mathcal U\subseteq\mathbb R^m_+$, let $\mu_j=\max\{b_j:b\in\mathcal U\}$ for each $j$, and consider any complete run of Algorithm $\mathcal A$ with $K$ iterations and choices $u^1,\dots,u^K$, with output $\beta=u^1+\dots+u^K$ and partition $J_1,J_2$. Then for every $b\in\mathcal U$,
--   $$\sum_{j\in J_1}\frac{b_j}{\mu_j}\le\sqrt m,$$
--   and $b_j\le\beta_j$ for all $j\in J_2$.
--
--   The two properties are exactly what the affine policy of Theorem 4 needs: coordinates in $J_1$ are covered by the linear part of the policy at cost $\sqrt m$, and coordinates in $J_2$ are dominated by the fixed vector $\beta$.
--
--   **Formalization Note** The statement holds for every run of the algorithm (the argmax choices are not unique). $J_2$ is the complement of $J_1$. Positivity of $\mu$, convexity, compactness and full-dimensionality of $\mathcal U$ are not assumed.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Lemma 9, PDF p. 28

import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix

namespace AffinePolicies.SqrtBound

theorem lemma_9 {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u) :
    (∀ b ∈ U, scaledSum μ (J1 μ u K) b ≤ Real.sqrt m) ∧
      ∀ j, j ∉ J1 μ u K → ∀ b ∈ U, b j ≤ betaSum u K j := by sorry

end AffinePolicies.SqrtBound
