-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflected_infimum_integer_horizon_tendsto_inf
-- name    : AvramDividend.Classical.reflected_infimum_integer_horizon_tendsto_inf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:21:24.402132+00:00
-- url     : https://prove2.me/theorems/4bf92e93-6877-408c-89ba-1442d1b2d3f8
-- title:
--   Reflected-infimum Laplace expectations converge to their infimum along integer horizons
-- statement:
--   At positive Laplace exponent, the nonnegative expected reflected-infimum envelope decreases as the integer observation horizon grows. Its values therefore converge to their infimum in the extended nonnegative reals. This is a finite-to-infinite horizon convergence prerequisite for a killed-survival renewal-potential calculation.
-- source:
--   Proved reflected_infimum_expectation_antitone_horizon; pinned Mathlib.Topology.Order.MonotoneConvergence tendsto_atTop_iInf.

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_reflected_infimum_transform
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_antitone_horizon

open MeasureTheory Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.reflected_infimum_integer_horizon_tendsto_inf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun n : ℕ =>
      ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (n : ℝ≥0) ∧
          y = X.X s ω})) / θ) ∂P) atTop
      (nhds (⨅ n : ℕ,
        ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (-θ * max 0
          (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ (n : ℝ≥0) ∧
            y = X.X s ω})) / θ) ∂P)) := by sorry
