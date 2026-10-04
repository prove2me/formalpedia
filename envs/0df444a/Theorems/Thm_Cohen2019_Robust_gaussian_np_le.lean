-- Prove2me | Theorems.Thm_Cohen2019_Robust_gaussian_np_le
-- name    : Cohen2019.Robust.gaussian_np_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:03:03.878142+00:00
-- url     : https://prove2.me/theorems/b31f305d-8901-4d54-9fcb-6e8557bf8373
-- title:
--   Lemma 4, part 1 — Neyman–Pearson for Gaussians with different means, half-space $\{\delta^\top z \le \beta\}$
-- statement:
--   Let $\sigma > 0$, $x, \delta \in \mathbb R^d$, $X \sim \mathcal N(x, \sigma^2 I)$ and $Y \sim \mathcal N(x + \delta, \sigma^2 I)$. Let $h : \mathbb R^d \to \{0,1\}$ be any deterministic or random function, described by $h(1\mid z) \in [0,1]$. Let $\beta \in \mathbb R$ and
--   $$
--   S = \{z \in \mathbb R^d : \delta^\top z \le \beta\}.
--   $$
--   If $\mathbb P(h(X) = 1) \ge \mathbb P(X \in S)$, then
--   $$
--   \mathbb P(h(Y) = 1) \ge \mathbb P(Y \in S).
--   $$
--
--   In the proof of Theorem 1 this is applied with $h(z) = \mathbb P(f(z) = c_A)$: it shows that, among all classifiers with the observed probability of $c_A$ at $x$, a linear one with decision boundary orthogonal to $\delta$ has the least probability of $c_A$ at $x + \delta$.
--
--   **Formalization Note** $\mathcal N(x,\sigma^2 I)$ is `gaussNoise x σ`; $h$ is a measurable $[0,1]$-valued function and $\mathbb P(h(X) = 1) = \int h\,d\mathcal N(x,\sigma^2 I)$.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Lemma 4, part 1, p. 12 (PDF page)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Model

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- **Lemma 4 (Neyman–Pearson for Gaussians with different means), part 1.** Cohen, Rosenfeld,
Kolter, *Certified Adversarial Robustness via Randomized Smoothing*, arXiv:1902.02918v2, Lemma 4,
p. 12 (PDF page). Let `X ∼ 𝒩(x, σ²I)`, `Y ∼ 𝒩(x + δ, σ²I)`, `h : ℝᵈ → {0,1}` deterministic or
random. If `S = {z : δᵀz ≤ β}` for some `β` and `ℙ(h(X) = 1) ≥ ℙ(X ∈ S)`, then
`ℙ(h(Y) = 1) ≥ ℙ(Y ∈ S)`.

**Formalization Note.** `𝒩(x, σ²I) = gaussNoise x σ` with `σ > 0` (the paper's standing noise
level). A random `h` is its probability `h(1|z) ∈ [0,1]` of returning `1`, so
`ℙ(h(X) = 1) = ∫ h d𝒩(x, σ²I)`. `δᵀz` is `inner ℝ δ z`. -/
theorem gaussian_np_le {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (x δ : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h) (hh01 : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (hX : (gaussNoise x σ {z | inner ℝ δ z ≤ β}).toReal ≤ ∫ z, h z ∂(gaussNoise x σ)) :
    (gaussNoise (x + δ) σ {z | inner ℝ δ z ≤ β}).toReal
      ≤ ∫ z, h z ∂(gaussNoise (x + δ) σ) := by sorry

end Cohen2019.Robust
