-- Prove2me | Theorems.Thm_ActuarialValuation_exMax_one
-- name    : ActuarialValuation.exMax_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:11:36.314235+00:00
-- url     : https://prove2.me/theorems/c6b30f16-5f41-46b2-b1a5-3a9727291b46
-- title:
--   Gumbel and generalized extreme-value maxima: exMax_one
-- statement:
--   A single insured loss is its own sample maximum. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem exMax_one (F : ℝ → ℝ) (x : ℝ) : exMaxOfIndependent F 1 x=F x := by sorry

end ActuarialValuation
