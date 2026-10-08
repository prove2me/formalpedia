-- Prove2me | Theorems.Thm_BurkholderDFI_SquareFnLp_eq_1_3
-- name    : BurkholderDFI.SquareFnLp.eq_1_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:54:16.650809+00:00
-- url     : https://prove2.me/theorems/d64ad652-1f45-4e3f-bb71-fe07fada9602
-- title:
--   (1.2)–(1.3) — λP(Y > βλ) ≤ α∫_{Y>λ} X for all λ > 0 implies ‖Y‖_p ≤ αβ^p q‖X‖_p (cited)
-- statement:
--   Let $X$ and $Y$ be nonnegative random variables (possibly taking the value $+\infty$) on a probability space, and let $\alpha > 0$ and $\beta \ge 1$. Suppose that
--   $$\lambda\, P(Y > \beta\lambda) \le \alpha \int_{\{Y > \lambda\}} X \, dP \qquad \text{for all } \lambda > 0. \tag{1.2}$$
--   Then for every $1 < p < \infty$, with conjugate exponent $q$ ($p^{-1} + q^{-1} = 1$),
--   $$\|Y\|_p \le \alpha \beta^p q\, \|X\|_p. \tag{1.3}$$
--
--   Burkholder calls this classical (Doob proves it for $\alpha = \beta = 1$). It is the device that turns the distribution function inequality (3.4) into the moment inequality (3.5).
--
--   **Formalization Note** $X$ and $Y$ are measurable and $[0, \infty]$-valued, and $\|\cdot\|_p = (E(\cdot)^p)^{1/p}$ is computed in $[0, \infty]$, so both sides may be infinite; the inequality then reads in the extended sense. The conjugate exponent is determined by $p^{-1} + q^{-1} = 1$, which forces $q > 1$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §1, p. 20, displays (1.2)–(1.3) (classical; Doob [15] for α = β = 1)

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.SquareFnLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem eq_1_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ≥0∞) (hX : Measurable X) (hY : Measurable Y)
    (α β : ℝ) (hα : 0 < α) (hβ : 1 ≤ β)
    (h12 : ∀ l : ℝ, 0 < l →
      ENNReal.ofReal l * P {ω | ENNReal.ofReal (β * l) < Y ω}
        ≤ ENNReal.ofReal α * ∫⁻ ω in {ω | ENNReal.ofReal l < Y ω}, X ω ∂P)
    (p q : ℝ) (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    lpNormE P p Y ≤ ENNReal.ofReal (α * β ^ p * q) * lpNormE P p X := by sorry

end BurkholderDFI.SquareFnLp
