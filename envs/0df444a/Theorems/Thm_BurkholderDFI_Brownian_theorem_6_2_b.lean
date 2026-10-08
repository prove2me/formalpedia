-- Prove2me | Theorems.Thm_BurkholderDFI_Brownian_theorem_6_2_b
-- name    : BurkholderDFI.Brownian.theorem_6_2_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:19.435533+00:00
-- url     : https://prove2.me/theorems/14c22ea1-c7ba-4365-a9e6-5137eab3b84f
-- title:
--   Theorem 6.2 (6.4) — $P(X^*(\tau)>\beta\lambda,\ \tau^{1/2}\le\delta\lambda)\le\frac{\delta^2}{(\beta-1)^2}P(X^*(\tau)>\lambda)$
-- statement:
--   Let $X$ be a one-dimensional Brownian motion with continuous sample functions, $\tau$ a stopping time of $X$ (possibly infinite), and $X^*(\tau)=\sup_{t\ge0}|X(\tau\wedge t)|$. Let $\beta>1$ and $\delta>0$. Then for every $\lambda>0$,
--   $$P\big(X^*(\tau)>\beta\lambda,\ \tau^{1/2}\le\delta\lambda\big)\le\frac{\delta^2}{(\beta-1)^2}\,P\big(X^*(\tau)>\lambda\big). \tag{6.4}$$
--
--   This is the companion good-$\lambda$ inequality with the roles of $\tau^{1/2}$ and $X^*(\tau)$ exchanged; note that its constant $\delta^2/(\beta-1)^2$ differs from the constant $\delta^2/(\beta^2-1)$ of (6.3). Combined with Lemma 7.1 it yields the right-hand inequality of Theorem 6.1.
--
--   **Formalization Note** $\tau^{1/2}$ and $X^*(\tau)$ take values in $[0,\infty]$, with $\infty^{1/2}=\infty$; $\tau$ is not assumed finite. The strict and non-strict inequalities are those of the page.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 6.2, (6.4), p. 26

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Definitions.Def_BurkholderDFI_Brownian_Process
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.Brownian

/-- Theorem 6.2, (6.4), p. 26: `P(X*(τ) > βλ, τ^{1/2} ≤ δλ) ≤ δ²/(β − 1)² · P(X*(τ) > λ)`. -/
theorem theorem_6_2_b {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsBM X P) (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTimeOf X τ)
    (β δ : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (l : ℝ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < maxStopped X (τ ω) ω ∧
        τ ω ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (δ * l)}
      ≤ ENNReal.ofReal (δ ^ 2 / (β - 1) ^ 2) * P {ω | ENNReal.ofReal l < maxStopped X (τ ω) ω} := by sorry

end BurkholderDFI.Brownian
