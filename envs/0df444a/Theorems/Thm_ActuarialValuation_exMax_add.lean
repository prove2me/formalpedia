-- Prove2me | Theorems.Thm_ActuarialValuation_exMax_add
-- name    : ActuarialValuation.exMax_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:11:50.863461+00:00
-- url     : https://prove2.me/theorems/4c929254-8845-46f8-bf9f-a77cac42d5ed
-- title:
--   Gumbel and generalized extreme-value maxima: exMax_add
-- statement:
--   Maxima of independent claim groups have multiplicative joint cumulative probability. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   G_{\xi}(x)=\exp\left[-\left(1+\xi\frac{x-\mu}{\sigma}\right)^{-1/\xi}\right]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. NIST, Conditional Mean Exceedance: generalized Pareto distribution, https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm; NIST, Extreme Value Type I Distribution, https://www.itl.nist.gov/div898/handbook/eda/section3/eda366g.htm; Annual Review of Statistics, Extreme Value Analysis for Financial Risk Management, https://doi.org/10.1146/annurev-statistics-042720-015705. Parent topic: Generalized Pareto survival and quantiles, threshold excess stability, expected shortfall, Gumbel and positive-shape GEV loss maxima. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exMaxOfIndependent

namespace ActuarialValuation

theorem exMax_add (F : ℝ → ℝ) (m n : ℕ) (x : ℝ) : exMaxOfIndependent F (m+n) x=exMaxOfIndependent F m x*exMaxOfIndependent F n x := by sorry

end ActuarialValuation
