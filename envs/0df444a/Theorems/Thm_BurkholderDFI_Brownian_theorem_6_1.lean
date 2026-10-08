-- Prove2me | Theorems.Thm_BurkholderDFI_Brownian_theorem_6_1
-- name    : BurkholderDFI.Brownian.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:15.812785+00:00
-- url     : https://prove2.me/theorems/7360c0ba-0d04-4be1-b2f7-327c01132640
-- title:
--   Theorem 6.1 — $cE\Phi(\tau^{1/2})\le E\Phi(X^*(\tau))\le CE\Phi(\tau^{1/2})$ for every stopping time τ of Brownian motion
-- statement:
--   Let $\Phi:[0,\infty]\to[0,\infty]$ be non-decreasing and continuous with $\Phi(0)=0$ and satisfying the growth condition
--   $$\Phi(2\lambda)\le c_{(6.1)}\,\Phi(\lambda),\qquad\lambda>0 .$$
--   Let $X$ be a one-dimensional Brownian motion with continuous sample functions on a probability space $(\Omega,\mathcal A,P)$, $\mathcal B(t)=\sigma\{X(s),0\le s\le t\}$, and $\tau:\Omega\to[0,\infty]$ a stopping time of $X$, i.e. $\{\tau<t\}\in\mathcal B(t)$ for $t>0$. Write $X^*(\tau)=\sup_{t\ge0}|X(\tau\wedge t)|$. Then
--   $$c\,E\Phi(\tau^{1/2})\le E\Phi(X^*(\tau))\le C\,E\Phi(\tau^{1/2}), \tag{6.2}$$
--   where the positive constants $c$ and $C$ depend only on the growth constant $c_{(6.1)}$.
--
--   For $\Phi(\lambda)=\lambda^p$, $0<p<\infty$, this says that $E\,X^*(\tau)^p$ and $E\,\tau^{p/2}$ are comparable for all stopping times, the Brownian prototype of the Burkholder–Davis–Gundy inequalities: the stopping time plays the role of the square function.
--
--   **Formalization Note** The paper states: "the choice of $c$ and $C$ depends only on $c_{(6.1)}$"; we state: for every $c_{(6.1)}\ge0$ there exist $c,C>0$ such that for every probability space (in universe `Type`), every Brownian motion, every stopping time and every $\Phi$ with growth constant $c_{(6.1)}$ the two inequalities hold. $\tau$ may be infinite; $\tau^{1/2}$, $X^*(\tau)$ and both expectations take values in $[0,\infty]$, so either side may be infinite. Stopping times are the paper's ($\{\tau<t\}$, raw natural filtration), Brownian motion has every path continuous and each $X(t)$ measurable. $\Phi\not\equiv0$ is not assumed (the statement is trivial for $\Phi\equiv0$), and the growth condition is required for all $\lambda\in[0,\infty]$, equivalent to the paper's by continuity.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 6.1, (6.2), p. 25

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Definitions.Def_BurkholderDFI_Brownian_Process
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.Brownian

/-- Theorem 6.1, (6.2), p. 25: `c EΦ(τ^{1/2}) ≤ EΦ(X*(τ)) ≤ C EΦ(τ^{1/2})` for every stopping
time `τ` of Brownian motion, with `c, C` depending only on the growth constant of (6.1). -/
theorem theorem_6_1 (c : ℝ≥0) :
    ∃ C₁ C₂ : ℝ≥0, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℝ≥0 → Ω → ℝ), IsBM X P → ∀ τ : Ω → ℝ≥0∞, IsStoppingTimeOf X τ →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
          (C₁ : ℝ≥0∞) * ∫⁻ ω, Φ (τ ω ^ (1 / 2 : ℝ)) ∂P ≤ ∫⁻ ω, Φ (maxStopped X (τ ω) ω) ∂P ∧
          ∫⁻ ω, Φ (maxStopped X (τ ω) ω) ∂P ≤ (C₂ : ℝ≥0∞) * ∫⁻ ω, Φ (τ ω ^ (1 / 2 : ℝ)) ∂P := by sorry

end BurkholderDFI.Brownian
