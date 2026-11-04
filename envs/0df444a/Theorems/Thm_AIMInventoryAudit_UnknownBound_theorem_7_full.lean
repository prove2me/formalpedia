-- Prove2me | Theorems.Thm_AIMInventoryAudit_UnknownBound_theorem_7_full
-- name    : AIMInventoryAudit.UnknownBound.theorem_7_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:32:59.891313+00:00
-- url     : https://prove2.me/theorems/46f4926d-8eba-4248-96c3-0ce72cc596ff
-- title:
--   Theorem 7 — full-domain regret of AIM without a known newsvendor bound
-- statement:
--   Let $\mu$ be any probability law of finite nonnegative real demand and let $D_1,D_2,\ldots$ be its IID path. Let $h,b\ge0$ with $B=\max\{b,h\}>0$. Put $q=\inf\{y\ge0:F(y)\ge b/(b+h)\}$, where $F(y)=\mathbb P(D\le y)$; only at $h=0$ require this set to be nonempty. For $0<\delta<1/2$, deterministic $\hat y_1^\delta\in[0,1]$ and every integer $T\ge1$, run
--
--   $$\hat y_{t+1}^\delta=\max\{\min\{\hat y_t^\delta-\epsilon_t H_t(\hat y_t^\delta),t^{\delta/2}\},0\},\quad\epsilon_t=1/(B\sqrt t),\quad H_t(y)=\begin{cases}h&D_t<y,\\-b&D_t\ge y.\end{cases}$$
--
--   Write $\ell(y,d)=h(y-d)^++b(d-y)^+$, $R(y)=\int[\ell(y,d)-\ell(q,d)]d\mu$ and $Q_e(y)=\int\ell(y,d)d\mu\in[0,\infty]$. When $Q_e(q)<\infty$, $Q$ denotes the genuine finite real cost.
--
--   Set
--
--   $$C(T,\delta,q)=B\left(T^{-(1/2-\delta)}+T^{-1/2}+\frac{q^{1+2/\delta}}T\right).$$
--
--   The critical set is nonempty, $q$ belongs to it, and $\ell(y,D)-\ell(q,D)$ is integrable at every finite real $y$. The average centered cost along the run is integrable and the following three conclusions hold:
--
--   1. $\displaystyle\mathbb E\left[\frac1T\sum_{t=1}^T R(\hat y_t^\delta)\right]\le C(T,\delta,q)$.
--   2. $\displaystyle\mathbb E\left[\frac1T\sum_{t=1}^T Q_e(\hat y_t^\delta)\right]\le Q_e(q)+C(T,\delta,q)$, with nonnegative extended integrals.
--   3. If $Q_e(q)<\infty$, then $Q_e(y)<\infty$ and $\ell(y,D)$ is integrable at every finite real $y$, $Q_e(y)$ is the nonnegative embedding of $Q(y)$, and the random average of $Q(\hat y_t^\delta)$ is integrable. Moreover its real regret equals the centered expectation and
--
--   $$\mathbb E\left[\frac1T\sum_{t=1}^T Q(\hat y_t^\delta)\right]-Q(q)\le B\left(\frac1{T^{1/2-\delta}}+\frac1{T^{1/2}}+\frac{q^{1+2/\delta}}T\right).$$
--
--   This is the exact quantitative guarantee for the sales-driven perishable policy. Its actions use neither the law, its quantile, a bound on that quantile, nor the horizon. For Pareto demand supported on $[1,\infty)$ with tail $x^{-1/2}$ and $b=h=1$, $q=4$ but every uncentered expected cost is infinite; conclusions 1 and 2 give a defined interpretation while conclusion 3 preserves every finite-cost source instance.
--
--   Differences from the source:
--   - reading: the modified algorithm leaves its initial target implicit → every deterministic initial target in [0,1]; reason: the proof uses stock in [0,t^(δ/2)] from t=1; unrestricted starts fail at D=0, b=h=1, initial 3, T=1
--   - generalization: the numerical Q-cost regret where real costs are defined → a real centered-regret bound and an additive extended-cost bound for every law, together with the exact finite-cost source formula; reason: centering before integration retains infinite-mean laws without infinity minus infinity and specializes to every originally defined source instance
--   - generalization: the usual positive-cost interpretation → nonnegative b,h with max(b,h)>0 and a nonempty critical set required only if h=0; reason: this includes all positive-cost instances and every defined zero-cost endpoint without an empty-infimum value
--   - encoding: finite expected quantities and a finite newsvendor level are used implicitly → integrability is concluded and critical-set nonemptiness must be derived from the probability law unless h=0, with extended nonnegative costs used to detect finiteness; reason: prevents real-integral or real-infimum defaults from replacing the mathematical quantities
--   - generalization: the sample loss and expected cost are defined for nonnegative stock levels → auxiliary loss-difference integrability and finite-cost identities hold for every real stock level; reason: the same loss formula has bounded differences at any two finite real levels, and restricting these auxiliary assertions to nonnegative levels recovers the source; policy stocks remain nonnegative
-- source:
--   Huh & Rusmevichientong (2009), A Nonparametric Asymptotic Analysis of Inventory Planning with Censored Demand, author’s manuscript associated with doi:10.1287/moor.1080.0355, https://doi.org/10.1287/moor.1080.0355, Theorem 7, printed p. 11 / PDF p. 11; proof Equations (10)–(11), printed p. 12 / PDF p. 12; model Equation (1), printed p. 6 / PDF p. 6.

import Mathlib
import Definitions.Def_AIMInventoryAudit_UnknownBound_Costs

open MeasureTheory
open scoped NNReal ENNReal BigOperators
open AIMInventory.UnknownBound

namespace AIMInventoryAudit.UnknownBound

/-- Theorem 7, p. 11: all three exact terms, every positive horizon and every interior δ.
The centered and additive extended clauses cover infinite-mean laws; the finite-cost
clause is the original real regret formula, with finiteness proved in the conclusion. -/
theorem theorem_7_full
    (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (T : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (hB : 0 < max b h) (hendpoint : h = 0 → (criticalSet μ h b).Nonempty)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (hT : 1 ≤ T) :
    (criticalSet μ h b).Nonempty ∧
    quantile μ h b ∈ criticalSet μ h b ∧
    (∀ y : ℝ, Integrable (fun d => loss h b y d - loss h b (quantile μ h b) d) μ) ∧
    Integrable (centeredAverage μ δ b h y₁ T) (pathLaw μ) ∧
    (∫ d, centeredAverage μ δ b h y₁ T d ∂pathLaw μ) ≤
      regretBound δ b h (quantile μ h b) T ∧
    (∫⁻ d, extendedAverage μ δ b h y₁ T d ∂pathLaw μ) ≤
      extendedCost μ h b (quantile μ h b) +
        ENNReal.ofReal (regretBound δ b h (quantile μ h b) T) ∧
    (extendedCost μ h b (quantile μ h b) < ⊤ →
      (∀ y : ℝ, extendedCost μ h b y < ⊤ ∧ Integrable (loss h b y) μ ∧
        ENNReal.ofReal (realCost μ h b y) = extendedCost μ h b y) ∧
      Integrable (realAverage μ δ b h y₁ T) (pathLaw μ) ∧
      (∫ d, realAverage μ δ b h y₁ T d ∂pathLaw μ) - realCost μ h b (quantile μ h b) =
        (∫ d, centeredAverage μ δ b h y₁ T d ∂pathLaw μ) ∧
      (∫ d, realAverage μ δ b h y₁ T d ∂pathLaw μ) - realCost μ h b (quantile μ h b) ≤
        regretBound δ b h (quantile μ h b) T) := by sorry

end AIMInventoryAudit.UnknownBound
