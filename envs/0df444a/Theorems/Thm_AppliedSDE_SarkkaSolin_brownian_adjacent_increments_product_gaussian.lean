-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_adjacent_increments_product_gaussian
-- name    : AppliedSDE.SarkkaSolin.brownian_adjacent_increments_product_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:56:59.483003+00:00
-- url     : https://prove2.me/theorems/85588f05-d0bd-4e15-ab29-fc3e42b5fab6
-- title:
--   Two adjacent Brownian increments jointly have independent centred Gaussian product law
-- statement:
--   For any Brownian motion W and nonnegative times r<=s<=t, the pair (W_s-W_r, W_t-W_s) has the product distribution of independent centred Gaussian variables with variances s-r and t-s. This exact joint law combines the proved Brownian independent-increments property and the Gaussian law of each increment, enabling a finite-dimensional deterministic-drift Girsanov shift of the original Brownian path.
-- source:
--   LevyStochCalc Brownian/MathlibBridge.lean; Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapter 7.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasIndepIncrements_readable
import Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_increment_gaussian_law
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian
open scoped NNReal

theorem AppliedSDE.SarkkaSolin.brownian_adjacent_increments_product_gaussian
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (r s t : ℝ≥0)
    (hrs : r ≤ s) (hst : s ≤ t) :
    HasLaw
      (fun ω => (W.W (s : ℝ) ω - W.W (r : ℝ) ω,
        W.W (t : ℝ) ω - W.W (s : ℝ) ω))
      ((gaussianReal 0 (s - r)).prod (gaussianReal 0 (t - s))) P := by
  sorry
