-- Prove2me | Theorems.Thm_ActuarialValuation_exExpectedShortfall_exceeds_quantile
-- name    : ActuarialValuation.exExpectedShortfall_exceeds_quantile
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:08:43.809613+00:00
-- url     : https://prove2.me/theorems/206ca865-20be-4128-93bc-be24d26ed391
-- title:
--   Extreme claim quantiles, threshold stability and expected shortfall: exExpectedShortfall_exceeds_quantile
-- statement:
--   Tail expected loss dominates the relevant loss quantile. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_exQuantile
import Definitions.Def_actuarial_exExpectedShortfall

namespace ActuarialValuation

theorem exExpectedShortfall_exceeds_quantile (xi sigma p : ℝ) (hxi0 : 0<xi) (hxi1 : xi<1) (hs : 0<sigma) (hp0 : 0≤p) (hp1 : p<1) : exQuantile xi sigma p≤exExpectedShortfall xi sigma p := by sorry

end ActuarialValuation
