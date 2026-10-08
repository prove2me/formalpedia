-- Prove2me | Theorems.Thm_ChoiceRM_MNL_lemma_5
-- name    : ChoiceRM.MNL.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:17.769951+00:00
-- url     : https://prove2.me/theorems/dc50fa19-2661-4b4f-9802-a65900421a51
-- title:
--   Lemma 5, p. 24 — a convex combination matching f(y) = y/(y+1) also matches g(y) = 1/(y+1)
-- statement:
--   Let $f(y) = \dfrac{y}{y+1}$ and $g(y) = \dfrac{1}{y+1}$. Suppose $0 \le y_1 \le y_2 \le y_3$ and $\theta \ge 0$ satisfy
--   $$
--   \theta f(y_1) + (1-\theta) f(y_3) = f(y_2).
--   $$
--   Then
--   $$
--   \theta g(y_1) + (1-\theta) g(y_3) = g(y_2).
--   $$
--
--   In the proof of Proposition 6 this transfers the choice of the weight $\theta$, made to match the total purchase probability of an incomplete set (equation (15)), to the individual MNL probabilities (equation (16)).
--
--   **Formalization Note** The paper's $\lambda$ is written $\theta$ (`λ` is reserved in Lean). The page says "$y_1 \le y_2 \le y_3$ and $\lambda$ are nonnegative numbers"; nonnegativity of $y_1$ gives that of $y_2, y_3$.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 24, Lemma 5

import Mathlib

namespace ChoiceRM.MNL

/-- Lemma 5, p. 24 (the paper's `λ` is written `θ`): with `f(y) = y/(y+1)` and `g(y) = 1/(y+1)`,
if `0 ≤ y₁ ≤ y₂ ≤ y₃`, `θ ≥ 0` and `θ f(y₁) + (1 − θ) f(y₃) = f(y₂)`, then
`θ g(y₁) + (1 − θ) g(y₃) = g(y₂)`. -/
theorem lemma_5 (y₁ y₂ y₃ θ : ℝ) (h0 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) (h23 : y₂ ≤ y₃) (hθ : 0 ≤ θ)
    (h : θ * (y₁ / (y₁ + 1)) + (1 - θ) * (y₃ / (y₃ + 1)) = y₂ / (y₂ + 1)) :
    θ * (1 / (y₁ + 1)) + (1 - θ) * (1 / (y₃ + 1)) = 1 / (y₂ + 1) := by sorry

end ChoiceRM.MNL
