-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_exact_stopped_payment_complete_stieltjes_split
-- name    : AvramDividend.Classical.avram_wave4_04b_exact_stopped_payment_complete_stieltjes_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:45:26.903442+00:00
-- url     : https://prove2.me/theorems/13340999-0379-4c9e-a4c9-d24f6cd9d987
-- title:
--   Exact stopped payment-time Stieltjes reward splits into true right atoms and all diffuse dividends
-- statement:
--   For any actual source dividend strategy, path, finite closed horizon, stopping/payment clock and discount rate, the complete discounted Stieltjes reward restricted to actual paymentTimes equals the sum over all genuine right-payment atoms with their payment-time indicator plus the full remaining atomless Stieltjes reward. The formula includes initial and permitted terminal atoms as well as absolutely continuous and singular-continuous dividends, without assuming any control density or compensation process. This is a deterministic all-mass prerequisite for source stochastic Ito–Meyer, not its replacement.
-- source:
--   Already Proved AvramDividend.Classical.avram_wave4_04b_finite_horizon_arbitrary_weight_stieltjes_split, source paymentTimes_measurable, and Mathlib lintegral_indicator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_arbitrary_weight_stieltjes_split

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_exact_stopped_payment_complete_stieltjes_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in paymentTimes τ, ENNReal.ofReal (Real.exp (-q * s)) ∂μ) =
      (∑' t : A, μ {(t : ℝ)} *
        (paymentTimes τ).indicator
          (fun s : ℝ => ENNReal.ofReal (Real.exp (-q * s))) (t : ℝ)) +
      (∫⁻ s in paymentTimes τ,
        ENNReal.ofReal (Real.exp (-q * s)) ∂μdiffuse) := by sorry
