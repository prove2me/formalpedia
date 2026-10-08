-- Prove2me | Theorems.Thm_AddLogReg_Discrete_eq_19
-- name    : AddLogReg.Discrete.eq_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:28.383789+00:00
-- url     : https://prove2.me/theorems/872c5dc1-d83a-4b01-9213-f72c37759163
-- title:
--   (19), p. 347 — −E_w[yf(x)] = E_w[(y − f(x))²]/2 − 1 for f(x) ∈ {−1, 1}
-- statement:
--   In the population setting of Discrete AdaBoost, let $F$ be measurable with $J(F) = E(e^{-yF(x)}) < \infty$, and let $E_w$ be the weighted expectation with weight $w(x, y) = e^{-yF(x)}$. For every measurable classifier $f$ with values in $\{-1, 1\}$,
--   $$-E_w[y f(x)] = \frac{E_w\big[(y - f(x))^2\big]}{2} - 1 .$$
--
--   Hence maximizing $E_w[yf(x)]$ is the same as minimizing the weighted squared error $E_w[(y - f(x))^2]$: the Newton-like step of Discrete AdaBoost is a weighted least-squares fit of a $\pm 1$-valued classifier.
--
--   **Formalization Note** The page prints $E_w[y - f(x)]^2/2$; the identity uses $f(x)^2 = y^2 = 1$ pointwise, so the square is inside the expectation, $E_w[(y - f(x))^2]/2$, and that is what is stated.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 347, (19)

import Mathlib
import Definitions.Def_AddLogReg_Discrete_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Discrete

/-- (19), p. 347: for a measurable `f` with values in `{−1, 1}`,
`−E_w[yf(x)] = E_w[(y − f(x))²]/2 − 1`. -/
theorem eq_19 {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (hF : Measurable F)
    (hJ : AddLogReg.ExpCrit.J ν F < ⊤) (f : X → ℝ) (hf : Measurable f) (hpm : IsPMOne f) :
    -wExp ν F (fun x b => AddLogReg.ExpCrit.sgn b * f x) =
      wExp ν F (fun x b => (AddLogReg.ExpCrit.sgn b - f x) ^ 2) / 2 - 1 := by sorry

end AddLogReg.Discrete
