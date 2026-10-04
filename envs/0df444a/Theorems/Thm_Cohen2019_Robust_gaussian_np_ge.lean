-- Prove2me | Theorems.Thm_Cohen2019_Robust_gaussian_np_ge
-- name    : Cohen2019.Robust.gaussian_np_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:03:18.374111+00:00
-- url     : https://prove2.me/theorems/1f41a7f5-2743-41c8-bac1-822b3bda005f
-- title:
--   Lemma 4, part 2 — Neyman–Pearson for Gaussians with different means, half-space $\{\delta^\top z \ge \beta\}$
-- statement:
--   Let $\sigma > 0$, $x, \delta \in \mathbb R^d$, $X \sim \mathcal N(x, \sigma^2 I)$ and $Y \sim \mathcal N(x + \delta, \sigma^2 I)$. Let $h : \mathbb R^d \to \{0,1\}$ be any deterministic or random function, described by $h(1\mid z) \in [0,1]$. Let $\beta \in \mathbb R$ and
--   $$
--   S = \{z \in \mathbb R^d : \delta^\top z \ge \beta\}.
--   $$
--   If $\mathbb P(h(X) = 1) \le \mathbb P(X \in S)$, then
--   $$
--   \mathbb P(h(Y) = 1) \le \mathbb P(Y \in S).
--   $$
--
--   In the proof of Theorem 1 this is applied with $h(z) = \mathbb P(f(z) = c_B)$ for a runner-up class $c_B$: a linear classifier with boundary orthogonal to $\delta$ maximizes the probability of $c_B$ at $x + \delta$ given its probability at $x$.
--
--   **Formalization Note** As for part 1.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Lemma 4, part 2, p. 13 (PDF page)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Model

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- **Lemma 4 (Neyman–Pearson for Gaussians with different means), part 2.** Cohen, Rosenfeld,
Kolter, *Certified Adversarial Robustness via Randomized Smoothing*, arXiv:1902.02918v2, Lemma 4,
p. 13 (PDF page). Let `X ∼ 𝒩(x, σ²I)`, `Y ∼ 𝒩(x + δ, σ²I)`, `h : ℝᵈ → {0,1}` deterministic or
random. If `S = {z : δᵀz ≥ β}` for some `β` and `ℙ(h(X) = 1) ≤ ℙ(X ∈ S)`, then
`ℙ(h(Y) = 1) ≤ ℙ(Y ∈ S)`.

**Formalization Note.** As for part 1 (`gaussian_np_le`). -/
theorem gaussian_np_ge {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (x δ : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h) (hh01 : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (hX : ∫ z, h z ∂(gaussNoise x σ) ≤ (gaussNoise x σ {z | β ≤ inner ℝ δ z}).toReal) :
    ∫ z, h z ∂(gaussNoise (x + δ) σ)
      ≤ (gaussNoise (x + δ) σ {z | β ≤ inner ℝ δ z}).toReal := by sorry

end Cohen2019.Robust
