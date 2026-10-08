-- Prove2me | Theorems.Thm_Cohen2019_Robust_likelihood_ratio
-- name    : Cohen2019.Robust.likelihood_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:33:11.518064+00:00
-- url     : https://prove2.me/theorems/bf3da223-653d-469e-ac29-f29b406f5b10
-- title:
--   Proof of Lemma 4, (5) — the Gaussian likelihood ratio is $\exp(a\,\delta^\top z + b)$
-- statement:
--   Let $\sigma > 0$, $x, \delta \in \mathbb R^d$, and let $\mu_X$, $\mu_Y$ be the densities of $X \sim \mathcal N(x, \sigma^2 I)$ and $Y \sim \mathcal N(x + \delta, \sigma^2 I)$. Then:
--
--   1. for every $z \in \mathbb R^d$,
--   $$
--   \mu_Y(z) = \exp\big(a\,\delta^\top z + b\big)\,\mu_X(z), \qquad a = \frac{1}{\sigma^2},\quad b = -\frac{2\delta^\top x + \|\delta\|^2}{2\sigma^2};
--   $$
--   2. for every $\beta \in \mathbb R$ there is some $t > 0$ such that
--   $$
--   \{z : \delta^\top z \le \beta\} = \{z : \mu_Y(z) \le t\,\mu_X(z)\}
--   \quad\text{and}\quad
--   \{z : \delta^\top z \ge \beta\} = \{z : \mu_Y(z) \ge t\,\mu_X(z)\}. \qquad (5)
--   $$
--
--   Statement 2 says that the half-spaces orthogonal to $\delta$ are exactly the likelihood-ratio sets of Lemma 3; this is what reduces Lemma 4 to Lemma 3.
--
--   **Formalization Note** The ratio $\mu_Y/\mu_X$ of the paper is written multiplied out (both densities are positive). The densities are `gaussDens x σ` and `gaussDens (x + δ) σ`.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Lemma 4, proof, eq. (5) and the likelihood-ratio display, p. 13 (PDF page)

import Mathlib
import Definitions.Def_Cohen2019_Robust_gaussDens

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- **Proof of Lemma 4: the Gaussian likelihood ratio and (5).** Cohen, Rosenfeld, Kolter, *Certified
Adversarial Robustness via Randomized Smoothing*, arXiv:1902.02918v2, Lemma 4, proof, eq. (5),
p. 13 (PDF page). For `X ∼ 𝒩(x, σ²I)`, `Y ∼ 𝒩(x + δ, σ²I)` with densities `μ_X`, `μ_Y`,
`μ_Y(z)/μ_X(z) = exp(a δᵀz + b)` with `a = 1/σ²`, `b = −(2δᵀx + ‖δ‖²)/(2σ²)`; and for any `β`
there is some `t > 0` with `{z : δᵀz ≤ β} = {z : μ_Y(z)/μ_X(z) ≤ t}` and
`{z : δᵀz ≥ β} = {z : μ_Y(z)/μ_X(z) ≥ t}` (5).

**Formalization Note.** `μ_X = gaussDens x σ`, `μ_Y = gaussDens (x + δ) σ`, both positive, so the
ratio identity is written as `μ_Y(z) = exp(a δᵀz + b) μ_X(z)` and the ratio sets of (5) are
written multiplied out, `{z : μ_Y(z) ≤ t μ_X(z)}`, `{z : t μ_X(z) ≤ μ_Y(z)}`. `δᵀz` is `inner ℝ δ z`. -/
theorem likelihood_ratio {d : ℕ} (σ : ℝ) (hσ : 0 < σ) (x δ : EuclideanSpace ℝ (Fin d)) :
    (∀ z, gaussDens (x + δ) σ z
      = Real.exp (1 / σ ^ 2 * inner ℝ δ z + -(2 * inner ℝ δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2))
        * gaussDens x σ z) ∧
    (∀ β : ℝ, ∃ t : ℝ, 0 < t ∧
      {z | inner ℝ δ z ≤ β} = {z | gaussDens (x + δ) σ z ≤ t * gaussDens x σ z} ∧
      {z | β ≤ inner ℝ δ z} = {z | t * gaussDens x σ z ≤ gaussDens (x + δ) σ z}) := by sorry

end Cohen2019.Robust
