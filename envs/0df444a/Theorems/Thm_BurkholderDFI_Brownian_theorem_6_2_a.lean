-- Prove2me | Theorems.Thm_BurkholderDFI_Brownian_theorem_6_2_a
-- name    : BurkholderDFI.Brownian.theorem_6_2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:26.256771+00:00
-- url     : https://prove2.me/theorems/ce66960a-284f-4be2-9779-a607be970b7f
-- title:
--   Theorem 6.2 (6.3) — $P(\tau^{1/2}>\beta\lambda,\ X^*(\tau)\le\delta\lambda)\le\frac{\delta^2}{\beta^2-1}P(\tau^{1/2}>\lambda)$
-- statement:
--   Let $X$ be a one-dimensional Brownian motion with continuous sample functions, $\tau$ a stopping time of $X$ (possibly infinite), and $X^*(\tau)=\sup_{t\ge0}|X(\tau\wedge t)|$. Let $\beta>1$ and $\delta>0$. Then for every $\lambda>0$,
--   $$P\big(\tau^{1/2}>\beta\lambda,\ X^*(\tau)\le\delta\lambda\big)\le\frac{\delta^2}{\beta^2-1}\,P\big(\tau^{1/2}>\lambda\big). \tag{6.3}$$
--
--   This is a "good-$\lambda$" inequality: the square root of the stopping time rarely exceeds a large multiple of $\lambda$ while the stopped maximal function stays small. Combined with Lemma 7.1 it yields the left-hand inequality of Theorem 6.1.
--
--   **Formalization Note** $\tau^{1/2}$ and $X^*(\tau)$ take values in $[0,\infty]$, with $\infty^{1/2}=\infty$; $\tau$ is not assumed finite. Thresholds $\beta\lambda$, $\delta\lambda$, $\lambda$ are positive reals; the strict and non-strict inequalities are those of the page.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 6.2, (6.3), p. 26

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Definitions.Def_BurkholderDFI_Brownian_Process
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.Brownian

/-- Theorem 6.2, (6.3), p. 26: `P(τ^{1/2} > βλ, X*(τ) ≤ δλ) ≤ δ²/(β² − 1) · P(τ^{1/2} > λ)`. -/
theorem theorem_6_2_a {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsBM X P) (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTimeOf X τ)
    (β δ : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (l : ℝ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < τ ω ^ (1 / 2 : ℝ) ∧
        maxStopped X (τ ω) ω ≤ ENNReal.ofReal (δ * l)}
      ≤ ENNReal.ofReal (δ ^ 2 / (β ^ 2 - 1)) * P {ω | ENNReal.ofReal l < τ ω ^ (1 / 2 : ℝ)} := by sorry

end BurkholderDFI.Brownian
