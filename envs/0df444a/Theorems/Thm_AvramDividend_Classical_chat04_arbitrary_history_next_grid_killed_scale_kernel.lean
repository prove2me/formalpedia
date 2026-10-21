-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_arbitrary_history_next_grid_killed_scale_kernel
-- name    : AvramDividend.Classical.chat04_arbitrary_history_next_grid_killed_scale_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:44:10.520877+00:00
-- url     : https://prove2.me/theorems/3a559405-05d1-4fcb-86cc-f71008d33f40
-- title:
--   Arbitrary-length historical survival and next-grid killed q-scale kernel
-- statement:
--   For a canonical spectrally negative Lévy process and arbitrary E-valued F_s-measurable history H, a measurable subset S of surviving histories, a measurable current-reserve map R:E→R and a canonical q-scale W, the expected future q-scale payoff restricted to having a surviving history H∈S and a nonnegative reserve R(H)+X_t−X_s at the next observation t equals the iterated product-measure integral of the same killed transition kernel over Law(H) and independent Law(X_(t−s)). This is a single generic n-to-n+1 finite-grid killed Markov recursion step, not a fixed two- or three-observation formula. The arbitrary history may encode every earlier observation and killed status, and the payoff is allowed infinite ENNReal mass. Its only stochastic input is the already accepted F_s-measurable arbitrary-statistic product law. It does not wrongly assert continuous-time killing or q-scale harmonicity.
-- source:
--   Accepted chat04_past_statistic_future_increment_product_law UUID 2e08771d-f678-4db6-825a-fc65503535c0; accepted chat03_scale_function_borel_measurable UUID 45cbe3b4-374d-4fa4-b988-e09f93b74cab; pinned Mathlib lintegral_map and lintegral_prod.

import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_past_statistic_future_increment_product_law
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat04_arbitrary_history_next_grid_killed_scale_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (S : Set E) (hS : MeasurableSet S)
    (R : E → ℝ) (hR : Measurable R) :
    (∫⁻ ω,
      if H ω ∈ S ∧ 0 ≤ R (H ω) + (X.X t ω - X.X s ω)
      then ENNReal.ofReal (W (R (H ω) + (X.X t ω - X.X s ω)))
      else 0 ∂P) =
      ∫⁻ z, ∫⁻ b,
        if z ∈ S ∧ 0 ≤ R z + b
        then ENNReal.ofReal (W (R z + b))
        else 0
        ∂(Measure.map (X.X (t - s)) P)
        ∂(Measure.map H P) := by sorry
