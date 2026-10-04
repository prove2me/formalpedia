-- Prove2me | Theorems.Thm_Cohen2019_Robust_certified_radius
-- name    : Cohen2019.Robust.certified_radius
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:03:59.046769+00:00
-- url     : https://prove2.me/theorems/3a132ce5-baa9-421a-af79-3757e0a985ec
-- title:
--   Theorem 1 — the Gaussian-smoothed classifier is constant on the $\ell_2$ ball of radius $\frac{\sigma}{2}(\Phi^{-1}(\underline{p_A}) - \Phi^{-1}(\overline{p_B}))$
-- statement:
--   Let $f : \mathbb R^d \to \mathcal Y$ be any deterministic or random function, let $\sigma > 0$ and $\varepsilon \sim \mathcal N(0, \sigma^2 I)$, and let
--   $$
--   g(x) = \arg\max_{c \in \mathcal Y} \mathbb P\big(f(x + \varepsilon) = c\big)
--   $$
--   be the smoothed classifier. Suppose that for a specific $x \in \mathbb R^d$ there exist $c_A \in \mathcal Y$ and $\underline{p_A}, \overline{p_B} \in [0,1]$ such that
--   $$
--   \mathbb P\big(f(x + \varepsilon) = c_A\big) \ \ge\ \underline{p_A} \ \ge\ \overline{p_B} \ \ge\ \mathbb P\big(f(x + \varepsilon) = c\big) \quad\text{for every } c \neq c_A. \qquad (6)
--   $$
--   Then $g(x + \delta) = c_A$ for every $\delta \in \mathbb R^d$ with $\|\delta\|_2 < R$, where
--   $$
--   R = \frac{\sigma}{2}\Big(\Phi^{-1}(\underline{p_A}) - \Phi^{-1}(\overline{p_B})\Big) \qquad (7)
--   $$
--   and $\Phi^{-1}$ is the inverse of the standard Gaussian CDF.
--
--   This is the robustness guarantee of randomized smoothing: from a lower bound on the probability of the top class and an upper bound on the probabilities of all others at a single point, the smoothed prediction is certified constant on a whole $\ell_2$ ball, with no assumption on $f$.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. A random $f$ is a map to probability distributions on $\mathcal Y$ with each $z \mapsto \mathbb P(f(z) = c)$ measurable; deterministic $f$ are the special case of point masses. $\mathcal Y$ is an arbitrary type, and "$\overline{p_B} \ge \max_{c \ne c_A}$" is stated class by class. "$g(x+\delta) = c_A$" means that $c_A$ is the unique maximizer, every other class having strictly smaller probability (the paper leaves $g$ undefined at ties). $R$ is an extended real with $\Phi^{-1}(0) = -\infty$ and $\Phi^{-1}(1) = +\infty$: it is $+\infty$ when $\underline{p_A} = 1 > \overline{p_B}$ or $\underline{p_A} > 0 = \overline{p_B}$, and in the two degenerate corners $\underline{p_A} = \overline{p_B} = 0$ and $\underline{p_A} = \overline{p_B} = 1$, where (7) reads $\infty - \infty$, $R = -\infty$ and the statement is vacuous.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Theorem 1, eqs. (2)–(3), p. 4; Theorem 1 (restated), eqs. (6)–(7), p. 13 (PDF pages)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Model

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- **Theorem 1 (robustness guarantee).** Cohen, Rosenfeld, Kolter, *Certified Adversarial Robustness
via Randomized Smoothing*, arXiv:1902.02918v2, Theorem 1, p. 4; restated as Theorem 1 (restated),
eqs. (6)–(7), p. 13 (PDF pages). Let `f : ℝᵈ → 𝒴` be any deterministic or random function, let
`ε ∼ 𝒩(0, σ²I)` and `g(x) = argmax_c ℙ(f(x + ε) = c)`. Suppose that for a specific `x ∈ ℝᵈ` there
exist `c_A ∈ 𝒴` and `p̲A, p̄B ∈ [0, 1]` with
`ℙ(f(x + ε) = c_A) ≥ p̲A ≥ p̄B ≥ max_{c ≠ c_A} ℙ(f(x + ε) = c)` (6). Then `g(x + δ) = c_A` for all
`‖δ‖₂ < R`, where `R = (σ/2)(Φ⁻¹(p̲A) − Φ⁻¹(p̄B))` (7).

**Formalization Note.** `ℝᵈ = EuclideanSpace ℝ (Fin d)`; `σ > 0` (the paper's noise level,
p. 4). A random `f` is `f : ℝᵈ → PMF 𝒴` with each `z ↦ ℙ(f(z) = c)` measurable; a deterministic
`f₀` is `fun z => PMF.pure (f₀ z)`. `𝒴` is an arbitrary type (no finiteness). "max over
`c ≠ c_A` ≤ p̄B" is stated as "every `c ≠ c_A` has probability ≤ p̄B". "`g(x + δ) = c_A`" is
`IsSmoothedPrediction`: `c_A` is the unique, strict maximizer of the class probabilities at
`x + δ`. `R = certRadius σ p̲A p̄B` is computed in `EReal` with `Φ⁻¹(0) = −∞`, `Φ⁻¹(1) = +∞`, so
`R = +∞` when `p̲A = 1 > p̄B` or `p̲A > 0 = p̄B`; in the two degenerate corners
`p̲A = p̄B ∈ {0, 1}` (the paper's `∞ − ∞`) `R = ⊥` and the conclusion is vacuous. -/
theorem certified_radius {d : ℕ} {Y : Type*} (f : EuclideanSpace ℝ (Fin d) → PMF Y)
    (hf : ∀ c : Y, Measurable fun z => f z c) (σ : ℝ) (hσ : 0 < σ)
    (x : EuclideanSpace ℝ (Fin d)) (cA : Y) (pA pB : ℝ)
    (hpA0 : 0 ≤ pA) (hpA1 : pA ≤ 1) (hpB0 : 0 ≤ pB) (hpB1 : pB ≤ 1)
    (hA : pA ≤ classProb f σ x cA) (hAB : pB ≤ pA)
    (hB : ∀ c : Y, c ≠ cA → classProb f σ x c ≤ pB) :
    ∀ δ : EuclideanSpace ℝ (Fin d), ((‖δ‖ : ℝ) : EReal) < certRadius σ pA pB →
      IsSmoothedPrediction f σ (x + δ) cA := by sorry

end Cohen2019.Robust
