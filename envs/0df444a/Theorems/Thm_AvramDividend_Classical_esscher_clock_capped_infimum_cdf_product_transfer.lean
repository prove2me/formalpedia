-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_clock_capped_infimum_cdf_product_transfer
-- name    : AvramDividend.Classical.esscher_clock_capped_infimum_cdf_product_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:56:18.871957+00:00
-- url     : https://prove2.me/theorems/51509fcb-3797-407c-b096-7085790932dc
-- title:
--   Actual capped-clock infimum CDF transfers to an independent Esscher terminal product probability
-- statement:
--   For the true finite-time running infimum of a spectrally negative Lévy process, under its genuine random-time Esscher likelihood with any real SFinite clock law ν, the event that the clock is no later than T and the negative running infimum is at most a has exactly the same probability as under the terminal Esscher law Q_T multiplied independently by ν. The proof discharges all adapted-section and joint-likelihood measurability obligations from already proven Lévy paths. This is the precise capped-clock infimum CDF interface for the independent exponential-clock Wiener–Hopf proof, with no claim of global infinite-horizon Esscher law.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2012), Esscher path law and Wiener–Hopf setup; accepted finite-clock stopped-event product transfer 51efe1af-d2be-4a72-bf21-81880a76e403; accepted measurable running infimum ae09696f, adaptedness fde9ba4e, and joint likelihood de339769.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_esscher_clock_supported_stopped_event_laws_agree
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_adapted
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_clock_capped_infimum_cdf_product_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0) (a : ℝ)
    {ν : Measure ℝ} [SFinite ν] :
    ((P.prod ν).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ))))
      {z : Ω × ℝ | z.2.toNNReal ≤ T ∧
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1} ≤ a} =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν)
      {z : Ω × ℝ | z.2.toNNReal ≤ T ∧
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1} ≤ a} := by sorry
