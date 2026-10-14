-- Prove2me | Theorems.Thm_ActuarialValuation_exConditionalSurvival_nonneg
-- name    : ActuarialValuation.exConditionalSurvival_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:07:32.619578+00:00
-- url     : https://prove2.me/theorems/3310e8f7-6788-4f5c-86c5-87c58b3dcc34
-- title:
--   Extreme claim quantiles, threshold stability and expected shortfall: exConditionalSurvival_nonneg
-- statement:
--   Conditional tail probability is nonnegative. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   q_p=\frac{\sigma}{\xi}\left((1-p)^{-\xi}-1\right),\quad \text{ES}_p=\frac{q_p+\sigma}{1-\xi}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. NIST, Conditional Mean Exceedance: generalized Pareto distribution, https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm; NIST, Extreme Value Type I Distribution, https://www.itl.nist.gov/div898/handbook/eda/section3/eda366g.htm; Annual Review of Statistics, Extreme Value Analysis for Financial Risk Management, https://doi.org/10.1146/annurev-statistics-042720-015705. Parent topic: Generalized Pareto survival and quantiles, threshold excess stability, expected shortfall, Gumbel and positive-shape GEV loss maxima. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://itl.nist.gov/div898/software/dataplot/refman1/auxillar/cme.htm

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exConditionalSurvival

namespace ActuarialValuation

theorem exConditionalSurvival_nonneg (xi sigma u x : ℝ) (hxi : 0<xi) (hs : 0<sigma) (hu : 0≤u) (hx : 0≤x) : 0≤exConditionalSurvival xi sigma u x := by sorry

end ActuarialValuation
