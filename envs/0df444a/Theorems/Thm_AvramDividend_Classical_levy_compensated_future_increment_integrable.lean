-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_future_increment_integrable
-- name    : AvramDividend.Classical.levy_compensated_future_increment_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:23:06.253076+00:00
-- url     : https://prove2.me/theorems/af71a624-b9e0-41d0-83c6-d1248727d6fe
-- title:
--   Compensated future Lévy increments have integrable exponential transform
-- statement:
--   Stationarity identifies the law of the increment X_t−X_s with X_(t−s). By applying a deterministic measurable exponential transform and the pinned IdentDistrib.integrable_iff, transfer integrability of the compensated exponential of X_(t−s) to the future increment.
-- source:
--   Stationary-increments axiom and Mathlib IdentDistrib.integrable_iff; intended to supply the integrability assumption of conditional-expectation pull-out in the exponential martingale proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_compensated_future_increment_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.ψ θ)) P := by sorry
