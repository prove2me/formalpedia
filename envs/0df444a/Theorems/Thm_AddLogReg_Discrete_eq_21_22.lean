-- Prove2me | Theorems.Thm_AddLogReg_Discrete_eq_21_22
-- name    : AddLogReg.Discrete.eq_21_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:03.688901+00:00
-- url     : https://prove2.me/theorems/da75421e-5339-4fde-848c-79d2e9500d18
-- title:
--   (21)–(22), p. 348 — ∂J(F + cf)/∂c = −E[e^{−y(F(x)+cf(x))}yf(x)], zero at the line-search c; E_w[yf(x)e^{−cyf(x)}] = 0
-- statement:
--   In the population setting of Discrete AdaBoost, let $F$ be measurable with $J(F) = E(e^{-yF(x)}) < \infty$ and let $f$ be a measurable classifier with values in $\{-1, 1\}$. Then:
--
--   1. the map $c \mapsto J(F + cf)$ is finite and differentiable on $\mathbb R$, with
--   $$\frac{\partial J(F + cf)}{\partial c} = -E\big[e^{-y(F(x) + cf(x))}\, y f(x)\big];$$
--   2. if moreover the weighted error $\mathrm{err} = E_w[1_{[y \neq f(x)]}]$ (weight $w(x, y) = e^{-yF(x)}$) satisfies $0 < \mathrm{err} < 1$, then at $c = \frac12 \log((1 - \mathrm{err})/\mathrm{err})$ this derivative vanishes, (21), and equivalently
--   $$E_w\big[y f(x) e^{-c y f(x)}\big] = 0. \tag{22}$$
--
--   These first-order conditions are the step from which the paper derives Corollary 2: after the reweighting $w \leftarrow w e^{-cyf(x)}$, the classifier $f$ has weighted error exactly one half.
--
--   **Formalization Note** $J(F + cf)$ is a lower integral in $[0, \infty]$; it is finite for every $c$ because $|f| = 1$ and $J(F) < \infty$, and the derivative is that of its real value.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 348, proof of Corollary 2 (21); (22)

import Mathlib
import Definitions.Def_AddLogReg_Discrete_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.Discrete

/-- (21)–(22), p. 348: for a measurable `f` with values in `{−1, 1}`, `c ↦ AddLogReg.ExpCrit.J(F + cf)` is
differentiable with `∂AddLogReg.ExpCrit.J(F + cf)/∂c = −E[e^{−y(F(x)+cf(x))} yf(x)]`; at the line-search
coefficient `c = ½ log((1 − err)/err)` (with `0 < err < 1`) this derivative vanishes, and
equivalently `E_w[yf(x)e^{−cyf(x)}] = 0`. -/
theorem eq_21_22 {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Bool)) [IsProbabilityMeasure ν] (F : X → ℝ) (hF : Measurable F)
    (hJ : AddLogReg.ExpCrit.J ν F < ⊤) (f : X → ℝ) (hf : Measurable f) (hpm : IsPMOne f) :
    (∀ c : ℝ, HasDerivAt (fun c' : ℝ => (AddLogReg.ExpCrit.J ν (F + c' • f)).toReal)
      (-∫ z, Real.exp (-(AddLogReg.ExpCrit.sgn z.2 * (F z.1 + c * f z.1))) * (AddLogReg.ExpCrit.sgn z.2 * f z.1) ∂ν) c) ∧
    (0 < err ν F f → err ν F f < 1 →
      (∫ z, Real.exp (-(AddLogReg.ExpCrit.sgn z.2 * (F z.1 + lineSearchCoeff (err ν F f) * f z.1))) *
          (AddLogReg.ExpCrit.sgn z.2 * f z.1) ∂ν) = 0 ∧
      wExp ν F (fun x b => AddLogReg.ExpCrit.sgn b * f x *
          Real.exp (-(lineSearchCoeff (err ν F f) * AddLogReg.ExpCrit.sgn b * f x))) = 0) := by sorry

end AddLogReg.Discrete
