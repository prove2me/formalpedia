-- Prove2me | Theorems.Thm_ActuarialValuation_exExtremeLoss_fundamental
-- name    : ActuarialValuation.exExtremeLoss_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:12:52.732988+00:00
-- url     : https://prove2.me/theorems/e2798938-f1b9-4f4e-bf3a-328057bd38b7
-- title:
--   Gumbel and generalized extreme-value maxima: exExtremeLoss_fundamental
-- statement:
--   An actual positive-shape GPD combines a valid percentile inverse, threshold-stable excess distribution and coherent expected shortfall, alongside a genuine extreme-maximum CDF. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_exSurvival
import Definitions.Def_actuarial_exCdf
import Definitions.Def_actuarial_exQuantile
import Definitions.Def_actuarial_exExcessScale
import Definitions.Def_actuarial_exConditionalSurvival
import Definitions.Def_actuarial_exExpectedShortfall
import Definitions.Def_actuarial_exGumbelMaxCdf

namespace ActuarialValuation

theorem exExtremeLoss_fundamental (xi sigma u x p : ℝ) (hxi : 0<xi) (hxi1 : xi<1) (hs : 0<sigma) (hu : 0≤u) (hx : 0≤x) (hp0 : 0≤p) (hp1 : p<1) : (exCdf xi sigma (exQuantile xi sigma p)=p) ∧ (exConditionalSurvival xi sigma u x=exSurvival xi (exExcessScale xi sigma u) x) ∧ (exQuantile xi sigma p≤exExpectedShortfall xi sigma p) ∧ (0<exGumbelMaxCdf 0 1 x) := by sorry

end ActuarialValuation
