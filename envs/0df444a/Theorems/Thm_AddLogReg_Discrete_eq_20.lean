-- Prove2me | Theorems.Thm_AddLogReg_Discrete_eq_20
-- name    : AddLogReg.Discrete.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:30.502888+00:00
-- url     : https://prove2.me/theorems/0d511d47-40f0-46d6-a3b1-a77ff1d6070c
-- title:
--   (20), p. 347 — c = argmin_c E_w e^{−cyf(x)} = ½ log((1 − err)/err), the unique minimizer
-- statement:
--   In the population setting of Discrete AdaBoost, let $F$ be measurable with $J(F) = E(e^{-yF(x)}) < \infty$, let $E_w$ be the weighted expectation with weight $w(x, y) = e^{-yF(x)}$, and let $f$ be a measurable classifier with values in $\{-1, 1\}$ whose weighted error $\mathrm{err} = E_w[1_{[y \neq f(x)]}]$ satisfies $0 < \mathrm{err} < 1$. Then
--   $$c = \frac12 \log \frac{1 - \mathrm{err}}{\mathrm{err}}$$
--   minimizes $c' \mapsto E_w\, e^{-c' y f(x)}$ over $c' \in \mathbb R$, and it is the only minimizer: any $c'$ with $E_w e^{-c'yf(x)} \le E_w e^{-cyf(x)}$ equals $c$.
--
--   This is the exact line search of Discrete AdaBoost. The coefficient is negative when $\mathrm{err} > 1/2$, which reverses the polarity of a weak learner that does worse than chance.
--
--   **Formalization Note** The hypothesis $0 < \mathrm{err} < 1$ is needed for the logarithm to be defined (Lean's `Real.log` returns $0$ on non-positive arguments); no condition $\mathrm{err} < 1/2$ is assumed.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 347, (20)

import Mathlib
import Definitions.Def_AddLogReg_Discrete_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Discrete

/-- (20), p. 347: for a measurable `f` with values in `{−1, 1}` and `0 < err < 1`, where
`err = E_w[1_{[y ≠ f(x)]}]`, the coefficient `c = ½ log((1 − err)/err)` is the unique minimizer
of `c' ↦ E_w e^{−c'yf(x)}` over `c' ∈ ℝ`. -/
theorem eq_20 {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (hF : Measurable F)
    (hJ : AddLogReg.ExpCrit.J ν F < ⊤) (f : X → ℝ) (hf : Measurable f) (hpm : IsPMOne f)
    (he0 : 0 < err ν F f) (he1 : err ν F f < 1) :
    (∀ c' : ℝ,
      wExp ν F (fun x b => Real.exp (-(lineSearchCoeff (err ν F f) * AddLogReg.ExpCrit.sgn b * f x))) ≤
        wExp ν F (fun x b => Real.exp (-(c' * AddLogReg.ExpCrit.sgn b * f x)))) ∧
    (∀ c' : ℝ,
      wExp ν F (fun x b => Real.exp (-(c' * AddLogReg.ExpCrit.sgn b * f x))) ≤
          wExp ν F (fun x b => Real.exp (-(lineSearchCoeff (err ν F f) * AddLogReg.ExpCrit.sgn b * f x))) →
        c' = lineSearchCoeff (err ν F f)) := by sorry

end AddLogReg.Discrete
