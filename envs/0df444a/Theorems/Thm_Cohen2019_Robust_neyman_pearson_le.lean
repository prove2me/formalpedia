-- Prove2me | Theorems.Thm_Cohen2019_Robust_neyman_pearson_le
-- name    : Cohen2019.Robust.neyman_pearson_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:06:51.011115+00:00
-- url     : https://prove2.me/theorems/7d727919-59bc-4179-a4af-3229e549ba16
-- title:
--   Lemma 3, part 1 — Neyman–Pearson for the set $\{\mu_Y \le t\,\mu_X\}$
-- statement:
--   Let $X$ and $Y$ be random variables in $\mathbb R^d$ with densities $\mu_X$ and $\mu_Y$ with respect to Lebesgue measure. Let $h : \mathbb R^d \to \{0,1\}$ be a random or deterministic function, described by $h(1 \mid z) \in [0,1]$, the probability that $h(z) = 1$; thus $\mathbb P(h(X) = 1) = \int h(1\mid z)\,\mu_X(z)\,dz$. Let $t > 0$ and
--   $$
--   S = \{z \in \mathbb R^d : \mu_Y(z) \le t\,\mu_X(z)\}.
--   $$
--   If $\mathbb P(h(X) = 1) \ge \mathbb P(X \in S)$, then
--   $$
--   \mathbb P(h(Y) = 1) \ge \mathbb P(Y \in S).
--   $$
--
--   This is one half of the Neyman–Pearson lemma in the form used to prove the robustness guarantee: among all tests with at least the acceptance probability of the likelihood-ratio set $S$ under $X$, the set $S$ has the smallest acceptance probability under $Y$.
--
--   **Formalization Note** The paper writes $S = \{z : \mu_Y(z)/\mu_X(z) \le t\}$; the set is stated multiplied out, which is exactly the property the paper's proof uses ($\mu_Y \le t\mu_X$ on $S$, $\mu_Y > t\mu_X$ off $S$) and avoids division by $\mu_X(z) = 0$. Densities are measurable maps to $[0,\infty]$ with integral $1$; the laws of $X$, $Y$ are Lebesgue measure with these densities; $h$ is a measurable $[0,1]$-valued function.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Lemma 3, part 1, p. 12 (PDF page)

import Mathlib

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- **Lemma 3 (Neyman–Pearson), part 1.** Cohen, Rosenfeld, Kolter, *Certified Adversarial
Robustness via Randomized Smoothing*, arXiv:1902.02918v2, Lemma 3, p. 12 (PDF page).
Let `X`, `Y` be random variables in `ℝᵈ` with densities `μ_X`, `μ_Y`, let `h : ℝᵈ → {0,1}` be random
or deterministic. If `S = {z : μ_Y(z)/μ_X(z) ≤ t}` for some `t > 0` and `ℙ(h(X) = 1) ≥ ℙ(X ∈ S)`,
then `ℙ(h(Y) = 1) ≥ ℙ(Y ∈ S)`.

**Formalization Note.** Densities are measurable `μX μY : ℝᵈ → ℝ≥0∞` with total Lebesgue mass 1;
the laws of `X`, `Y` are `volume.withDensity μX`, `volume.withDensity μY`. A random `h` is its
probability `h(1|z) ∈ [0,1]` of returning `1` (the paper's convention, p. 12), so
`ℙ(h(X) = 1) = ∫ h dℙ_X`; deterministic `h` are the indicator functions. The ratio set is written
multiplied out, `S = {z : μ_Y(z) ≤ t μ_X(z)}`: this is exactly the property the proof uses
("μ_Y(z) ≤ t μ_X(z) ∀z ∈ S and μ_Y(z) > t μ_X(z) ∀z ∈ Sᶜ", p. 12), and it avoids division by
`μ_X(z) = 0`. -/
theorem neyman_pearson_le {d : ℕ} (μX μY : EuclideanSpace ℝ (Fin d) → ENNReal)
    (hμX : Measurable μX) (hμY : Measurable μY)
    (hμX1 : ∫⁻ z, μX z = 1) (hμY1 : ∫⁻ z, μY z = 1)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h) (hh01 : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (t : ℝ) (ht : 0 < t)
    (hX : (volume.withDensity μX {z | μY z ≤ ENNReal.ofReal t * μX z}).toReal
      ≤ ∫ z, h z ∂(volume.withDensity μX)) :
    (volume.withDensity μY {z | μY z ≤ ENNReal.ofReal t * μX z}).toReal
      ≤ ∫ z, h z ∂(volume.withDensity μY) := by sorry

end Cohen2019.Robust
