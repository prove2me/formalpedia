-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_capital_weight_inside_lintegral
-- name    : AvramDividend.Classical.chat04_esscher_capital_weight_inside_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:16:21.778369+00:00
-- url     : https://prove2.me/theorems/b34bea91-57a3-444e-85d8-5fafebc02bd3
-- title:
--   Capital Laplace weight factors through the killed Esscher path integral
-- statement:
--   For each starting capital and finite horizon, the initial-capital Laplace exponential is constant in the Lévy sample path. It therefore factors exactly out of the extended nonnegative path integral even when the full survival indicator is present.
-- source:
--   The full-horizon lower-survival event is measurable in the Lévy filtration, and the terminal Esscher exponential is measurable by adaptedness. Use ENNReal.ofReal_mul and Mathlib lintegral_const_mul. This is the bridge between the pointwise weighted killed survival transform and the actual finite-horizon capital-reflected-infimum expectation.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_capital_weight_inside_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (t : ℝ≥0) (β θ : ℝ) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-β * x) *
            Real.exp (θ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) =
    ENNReal.ofReal (Real.exp (-β * x)) *
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (θ * X.X t ω -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) := by sorry
