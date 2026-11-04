-- Prove2me | Theorems.Thm_AIMInventoryAudit_UnknownBound_eq_11_full
-- name    : AIMInventoryAudit.UnknownBound.eq_11_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:32:35.410885+00:00
-- url     : https://prove2.me/theorems/9dd60f5b-615c-46dc-a108-e966a5e03ccd
-- title:
--   Equation (11) — late-round regret on the full demand domain
-- statement:
--   Let $\mu$ be any probability law of finite nonnegative real demand and let $D_1,D_2,\ldots$ be its IID path. Let $h,b\ge0$ with $B=\max\{b,h\}>0$. Put $q=\inf\{y\ge0:F(y)\ge b/(b+h)\}$, where $F(y)=\mathbb P(D\le y)$; only at $h=0$ require this set to be nonempty. For $0<\delta<1/2$, deterministic $\hat y_1^\delta\in[0,1]$ and every integer $T\ge1$, run
--
--   $$\hat y_{t+1}^\delta=\max\{\min\{\hat y_t^\delta-\epsilon_t H_t(\hat y_t^\delta),t^{\delta/2}\},0\},\quad\epsilon_t=1/(B\sqrt t),\quad H_t(y)=\begin{cases}h&D_t<y,\\-b&D_t\ge y.\end{cases}$$
--
--   Write $\ell(y,d)=h(y-d)^++b(d-y)^+$, $R(y)=\int[\ell(y,d)-\ell(q,d)]d\mu$ and $Q_e(y)=\int\ell(y,d)d\mu\in[0,\infty]$. When $Q_e(q)<\infty$, $Q$ denotes the genuine finite real cost.
--
--   For $I_+=\{t:1\le t\le T,\ q^{2/\delta}\le t\}$, the random centered sum is integrable and
--
--   $$\mathbb E\sum_{t\in I_+}R(\hat y_t^\delta)\le BT^{1/2+\delta}+BT^{1/2}.$$
--
--   If $Q_e(q)<\infty$, the random sum of $Q(\hat y_t^\delta)-Q(q)$ is integrable, its expectation equals the centered-sum expectation, and it satisfies the identical bound. This is the late-round contribution to Theorem 7. It includes an empty late set and does not require the horizon to reach the threshold.
--
--   Differences from the source:
--   - reading: the modified algorithm leaves its initial target implicit → every deterministic initial target in [0,1]; reason: the proof uses stock in [0,t^(δ/2)] from t=1; unrestricted starts fail at D=0, b=h=1, initial 3, T=1
--   - generalization: the numerical Q-cost difference where real costs are defined → the pointwise-centered real cost on every nonnegative demand law, retaining the exact Q-cost clause whenever Q_e(q) is finite; reason: Pareto tail P(D>x)=x^(-1/2) has q=4 at b=h=1 and Q_e(y)=infinity for all finite y, while the loss difference is integrable
--   - generalization: the usual positive-cost interpretation → nonnegative b,h with max(b,h)>0 and a nonempty critical set required only if h=0; reason: this includes all positive-cost instances and every defined zero-cost endpoint without an empty-infimum value
--   - encoding: finite expected quantities and a finite newsvendor level are used implicitly → integrability is concluded and critical-set nonemptiness must be derived from the probability law unless h=0, with extended nonnegative costs used to detect finiteness; reason: prevents real-integral or real-infimum defaults from replacing the mathematical quantities
--   - encoding: sum limits suppressed in (10) and (11) → sum over 1 through T, filtered by the strict early or weak late threshold; reason: the preceding equality fixes the finite horizon; q=0 gives an empty early set and late rounds start at one
-- source:
--   Huh & Rusmevichientong (2009), A Nonparametric Asymptotic Analysis of Inventory Planning with Censored Demand, author’s manuscript associated with doi:10.1287/moor.1080.0355, https://doi.org/10.1287/moor.1080.0355, §3.1, proof of Theorem 7, Equation (11), printed p. 12 / PDF p. 12.

import Mathlib
import Definitions.Def_AIMInventoryAudit_UnknownBound_Costs

open MeasureTheory
open scoped NNReal ENNReal BigOperators
open AIMInventory.UnknownBound

namespace AIMInventoryAudit.UnknownBound

/-- Equation (11), p. 12, on the full demand domain, including the source finite-cost clause. -/
theorem eq_11_full
    (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (T : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (hB : 0 < max b h) (hendpoint : h = 0 → (criticalSet μ h b).Nonempty)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (hT : 1 ≤ T) :
    let I := lateRounds δ (quantile μ h b) T
    Integrable (centeredSum μ δ b h y₁ I) (pathLaw μ) ∧
    (∫ d, centeredSum μ δ b h y₁ I d ∂pathLaw μ) ≤
      max b h * Real.rpow (T : ℝ) ((1 / 2 : ℝ) + δ) +
        max b h * Real.rpow (T : ℝ) (1 / 2 : ℝ) ∧
    (extendedCost μ h b (quantile μ h b) < ⊤ →
      Integrable (realGapSum μ δ b h y₁ I) (pathLaw μ) ∧
      (∫ d, realGapSum μ δ b h y₁ I d ∂pathLaw μ) =
        (∫ d, centeredSum μ δ b h y₁ I d ∂pathLaw μ) ∧
      (∫ d, realGapSum μ δ b h y₁ I d ∂pathLaw μ) ≤
        max b h * Real.rpow (T : ℝ) ((1 / 2 : ℝ) + δ) +
        max b h * Real.rpow (T : ℝ) (1 / 2 : ℝ)) := by sorry

end AIMInventoryAudit.UnknownBound
