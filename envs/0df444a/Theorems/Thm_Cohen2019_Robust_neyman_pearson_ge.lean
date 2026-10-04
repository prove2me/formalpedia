-- Prove2me | Theorems.Thm_Cohen2019_Robust_neyman_pearson_ge
-- name    : Cohen2019.Robust.neyman_pearson_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:06:56.39242+00:00
-- url     : https://prove2.me/theorems/dad4344a-86f9-49a9-90dd-6eab29bc7852
-- title:
--   Lemma 3, part 2 — Neyman–Pearson for the set $\{\mu_Y \ge t\,\mu_X\}$
-- statement:
--   Let $X$ and $Y$ be random variables in $\mathbb R^d$ with densities $\mu_X$ and $\mu_Y$, and let $h : \mathbb R^d \to \{0,1\}$ be a random or deterministic function, described by $h(1 \mid z) \in [0,1]$. Let $t > 0$ and
--   $$
--   S = \{z \in \mathbb R^d : \mu_Y(z) \ge t\,\mu_X(z)\}.
--   $$
--   If $\mathbb P(h(X) = 1) \le \mathbb P(X \in S)$, then
--   $$
--   \mathbb P(h(Y) = 1) \le \mathbb P(Y \in S).
--   $$
--
--   This is the classical Neyman–Pearson lemma: a test whose false-alarm probability under $X$ is at most that of the likelihood-ratio test $S$ has power under $Y$ at most that of $S$.
--
--   **Formalization Note** As in part 1: the ratio set $\{\mu_Y/\mu_X \ge t\}$ is written multiplied out, densities are measurable $[0,\infty]$-valued with integral $1$, and $h$ is a measurable $[0,1]$-valued function.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Lemma 3, part 2, p. 12 (PDF page)

import Mathlib

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- **Lemma 3 (Neyman–Pearson), part 2.** Cohen, Rosenfeld, Kolter, *Certified Adversarial
Robustness via Randomized Smoothing*, arXiv:1902.02918v2, Lemma 3, p. 12 (PDF page).
Let `X`, `Y` be random variables in `ℝᵈ` with densities `μ_X`, `μ_Y`, let `h : ℝᵈ → {0,1}` be random
or deterministic. If `S = {z : μ_Y(z)/μ_X(z) ≥ t}` for some `t > 0` and `ℙ(h(X) = 1) ≤ ℙ(X ∈ S)`,
then `ℙ(h(Y) = 1) ≤ ℙ(Y ∈ S)`.

**Formalization Note.** As for part 1 (`neyman_pearson_le`): densities `μX μY : ℝᵈ → ℝ≥0∞` with
mass 1, `h` the probability `h(1|z) ∈ [0,1]`, and the ratio set multiplied out,
`S = {z : t μ_X(z) ≤ μ_Y(z)}` ("μ_Y(z) ≥ t μ_X(z) on S, < on Sᶜ"). -/
theorem neyman_pearson_ge {d : ℕ} (μX μY : EuclideanSpace ℝ (Fin d) → ENNReal)
    (hμX : Measurable μX) (hμY : Measurable μY)
    (hμX1 : ∫⁻ z, μX z = 1) (hμY1 : ∫⁻ z, μY z = 1)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h) (hh01 : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (t : ℝ) (ht : 0 < t)
    (hX : ∫ z, h z ∂(volume.withDensity μX)
      ≤ (volume.withDensity μX {z | ENNReal.ofReal t * μX z ≤ μY z}).toReal) :
    ∫ z, h z ∂(volume.withDensity μY)
      ≤ (volume.withDensity μY {z | ENNReal.ofReal t * μX z ≤ μY z}).toReal := by sorry

end Cohen2019.Robust
