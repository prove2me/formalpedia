-- Prove2me | Theorems.Thm_AffinePolicies_SqrtBound_mu_pos
-- name    : AffinePolicies.SqrtBound.mu_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:40:06.778862+00:00
-- url     : https://prove2.me/theorems/b5e0211e-949a-4da0-a181-c8949404bd87
-- title:
--   (38), PDF p. 26 — μ_j = max{b_j : b ∈ 𝒰} is positive for a full-dimensional 𝒰 ⊆ ℝ^m_+
-- statement:
--   Let $\mathcal U\subseteq\mathbb R^m_+$ have nonempty interior, and for each coordinate $j$ let
--   $$\mu_j=\max\{b_j : b\in\mathcal U\}$$
--   (display (38); the maximum is assumed to be attained). Then
--   $$\mu_j>0\qquad\text{for all } j=1,\dots,m.$$
--
--   The positivity of $\mu_j$ is what makes the scaled sums $\sum_j b_j/\mu_j$ of Algorithm $\mathcal A$ and the policy of Theorem 4 well defined.
--
--   **Formalization Note** $\mu$ is a vector given together with the property that $\mu_j$ is the greatest element of $\{b_j : b\in\mathcal U\}$. Convexity and compactness of $\mathcal U$ are not needed and are not assumed.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, (38) and the sentence after it, PDF p. 26

import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix

namespace AffinePolicies.SqrtBound

theorem mu_pos {m : ℕ} (U : Set (Fin m → ℝ)) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUfull : (interior U).Nonempty)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j)) :
    ∀ j, 0 < μ j := by sorry

end AffinePolicies.SqrtBound
