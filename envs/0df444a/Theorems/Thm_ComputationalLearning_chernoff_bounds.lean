-- Prove2me | Theorems.Thm_ComputationalLearning_chernoff_bounds
-- name    : ComputationalLearning.chernoff_bounds
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:20:28.851214+00:00
-- url     : https://prove2.me/theorems/0f122cc0-d74f-477d-90dd-6f125327b7bd
-- title:
--   Theorem 9.2 (Chernoff bounds): additive and multiplicative tail bounds for m independent Bernoulli trials
-- statement:
--   **Theorem 9.2.** Let $X_1, \dots, X_m$ be a sequence of $m$ independent Bernoulli trials, each with probability of success $E[X_i] = p$. Let $S = X_1 + \dots + X_m$, so $E[S] = pm$. Then for $0 < \gamma \le 1$: (additive form) $\Pr[S > (p+\gamma)m] \le e^{-2m\gamma^2}$ and $\Pr[S < (p-\gamma)m] \le e^{-2m\gamma^2}$; (multiplicative form) $\Pr[S > (1+\gamma)pm] \le e^{-mp\gamma^2/3}$ and $\Pr[S < (1-\gamma)pm] \le e^{-mp\gamma^2/2}$.
--
--   Formally, on the product law of $m$ Bernoulli($p$) trials, $0 \le p \le 1$, the four bounds with non-strict inequalities in the events (stronger than the printed strict ones).
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, Chapter 9, §9.3 p. 190, Theorem 9.2

import Definitions.Def_ComputationalLearning_Boosting

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

/-- **Theorem 9.2 (Chernoff bounds)** (p. 190). Let `X₁, …, Xₘ` be independent Bernoulli trials
with success probability `p` and `S = X₁ + ⋯ + Xₘ`, so `E[S] = pm`. Then for `0 < γ ≤ 1`:
(additive form) `Pr[S ≥ (p + γ)m] ≤ e^{−2mγ²}` and `Pr[S ≤ (p − γ)m] ≤ e^{−2mγ²}`;
(multiplicative form) `Pr[S ≥ (1 + γ)pm] ≤ e^{−mpγ²/3}` and `Pr[S ≤ (1 − γ)pm] ≤ e^{−mpγ²/2}`. -/
theorem chernoff_bounds {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) :
    trialsLaw p m {ω | (p + γ) * m ≤ successes ω} ≤ ENNReal.ofReal (Real.exp (-(2 * m * γ ^ 2))) ∧
    trialsLaw p m {ω | (successes ω : ℝ) ≤ (p - γ) * m} ≤
      ENNReal.ofReal (Real.exp (-(2 * m * γ ^ 2))) ∧
    trialsLaw p m {ω | (1 + γ) * p * m ≤ successes ω} ≤
      ENNReal.ofReal (Real.exp (-(m * p * γ ^ 2 / 3))) ∧
    trialsLaw p m {ω | (successes ω : ℝ) ≤ (1 - γ) * p * m} ≤
      ENNReal.ofReal (Real.exp (-(m * p * γ ^ 2 / 2))) := by sorry

end ComputationalLearning
