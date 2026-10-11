-- Prove2me | Theorems.Thm_ActuarialValuation_exCdf_survival_balance
-- name    : ActuarialValuation.exCdf_survival_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:04:11.850982+00:00
-- url     : https://prove2.me/theorems/b2896d15-4514-4b66-8a2a-529fe9b32bcd
-- title:
--   Positive-shape generalized Pareto survival and severity density: exCdf_survival_balance
-- statement:
--   Severity CDF plus survival equals certainty. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_exSurvival
import Definitions.Def_actuarial_exCdf

namespace ActuarialValuation

theorem exCdf_survival_balance (xi sigma x : ℝ) : exCdf xi sigma x+exSurvival xi sigma x=1 := by sorry

end ActuarialValuation
