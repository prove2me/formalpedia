-- Prove2me | Theorems.Thm_ActuarialValuation_exDensity_nonneg
-- name    : ActuarialValuation.exDensity_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:04:40.391763+00:00
-- url     : https://prove2.me/theorems/99a43873-de3a-428c-b5ae-4176ef237cea
-- title:
--   Positive-shape generalized Pareto survival and severity density: exDensity_nonneg
-- statement:
--   A valid severity density cannot be negative. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   S(x)=\left(1+\frac{\xi x}{\sigma}\right)^{-1/\xi}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. NIST, Conditional Mean Exceedance: generalized Pareto distribution, https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm; NIST, Extreme Value Type I Distribution, https://www.itl.nist.gov/div898/handbook/eda/section3/eda366g.htm; Annual Review of Statistics, Extreme Value Analysis for Financial Risk Management, https://doi.org/10.1146/annurev-statistics-042720-015705. Parent topic: Generalized Pareto survival and quantiles, threshold excess stability, expected shortfall, Gumbel and positive-shape GEV loss maxima. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exDensity

namespace ActuarialValuation

theorem exDensity_nonneg (xi sigma x : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hx : 0≤x) : 0≤exDensity xi sigma x := by sorry

end ActuarialValuation
