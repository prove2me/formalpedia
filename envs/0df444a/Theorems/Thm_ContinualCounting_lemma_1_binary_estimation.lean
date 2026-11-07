-- Prove2me | Theorems.Thm_ContinualCounting_lemma_1_binary_estimation
-- name    : ContinualCounting.lemma_1_binary_estimation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:37.016025+00:00
-- url     : https://prove2.me/theorems/6b75345f-c2a6-42dd-9a18-fb251e42a802
-- title:
--   Lemma 1 [GV16] (corrected: bounded $\varepsilon$, $\delta\le\delta_0<1$) — private binary estimation needs noise
-- statement:
--   For every $\varepsilon_0>0$ and $\delta_0<1$ there is a constant $c>0$ such that the following holds for all $\varepsilon\in(0,\varepsilon_0]$ and $\delta\in[0,\delta_0]$. If $z$ is a real random variable with law $\nu$ and the mechanism $M(x)=x+z$ on $x\in\{0,1\}$, with $z$ independent of $x$, is $(\varepsilon,\delta)$-DP, then
--   $$\mathbb E[z^2]\ge c\min\{\varepsilon^{-2},\delta^{-2}\}=\frac{c}{\max\{\varepsilon,\delta\}^2}.$$
--
--   This is the statement that turns the adversary's linear measurement into a lower bound on the noise.
--
--   Differences from the source:
--   - correction: E[z²] = Ω(min{ε^{−2}, δ^{−2}}) for any (ε, δ)-DP mechanism, with no range on ε, δ → ∀ ε₀ > 0, ∀ δ₀ < 1, ∃ c > 0, for ε ∈ (0, ε₀], δ ∈ [0, δ₀]; reason: the printed form is false. (i) ε = 1, δ = 1 − η, z ∈ {−1, 0, 1} with Pr[z = ±1] = η/(1 + e) is (1, 1 − η)-DP with E z² = 2η/(1 + e) → 0 while min{ε^{−2}, δ^{−2}} → 1. (ii) δ = 0, Pr[z = k] ∝ e^{−ε|k|} on ℤ is ε-DP with E z² ~ 2e^{−ε} = o(ε^{−2}). The paper applies the lemma only at bounded ε and small δ
--   - encoding: min{ε^{−2}, δ^{−2}}; E[z²] → 1 / (max ε δ)²; `lintegral` of `enorm` squared; reason: equal for ε > 0, δ ≥ 0, including δ = 0; a non-integrable z² gives ∞
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Lemma 1, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_ContinualCounting_IsApproxDP

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **Lemma 1 [GV16] (corrected: bounded `ε`, `δ ≤ δ₀ < 1`).** Bairaktari, Dahl, Larsen, arXiv:2607.00876
(sha256 986e6426…), p.4: "Any (ε, δ)-DP mechanism M releasing a private binary variable x ∈ {0, 1} as
M(x) = x + z for a noise variable z independent of x must have E[z^2] = Ω(min{ε^{−2}, δ^{−2}})."

**Formalization Note.** The printed statement has no range and is false for `δ → 1` and for `ε → ∞`; the
hidden constant here depends on an upper bound `ε₀` of `ε` and a bound `δ₀ < 1` of `δ`. The paper uses the
lemma only at bounded `ε` and small `δ` (pp.28, 30). `min{ε^{−2}, δ^{−2}} = 1 / max{ε, δ}²`, also at `δ = 0`.
`ν` is the law of `z`, and the mechanism sends `x` to the law of `x + z`. The relation "the bits differ"
covers both orders of the pair `0, 1`. -/
theorem lemma_1_binary_estimation (ε₀ δ₀ : ℝ) (hε₀ : 0 < ε₀) (hδ₀ : δ₀ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε δ : ℝ, 0 < ε → ε ≤ ε₀ → 0 ≤ δ → δ ≤ δ₀ →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        IsApproxDP (fun a b : Bool => a ≠ b)
          (fun b : Bool => ν.map fun z => (if b then 1 else 0) + z) ε δ →
        ENNReal.ofReal (c / (max ε δ) ^ 2) ≤ ∫⁻ z, ‖z‖ₑ ^ 2 ∂ν := by sorry

end ContinualCounting
