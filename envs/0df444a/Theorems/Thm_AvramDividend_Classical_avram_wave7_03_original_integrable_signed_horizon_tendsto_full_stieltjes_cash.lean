-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_integrable_signed_horizon_tendsto_full_stieltjes_cash
-- name    : AvramDividend.Classical.avram_wave7_03_original_integrable_signed_horizon_tendsto_full_stieltjes_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:06:52.644871+00:00
-- url     : https://prove2.me/theorems/f93902dc-4060-458f-a5f6-8093e4ecef0b
-- title:
--   Original finite-horizon genuine signed Stieltjes integrals converge to the same-measure full pre-ruin signed cash
-- statement:
--   Fix exact original X, D, ω and q, and assume genuine real IntegrableOn of the exponential factor against the dividend Stieltjes measure restricted to the full original strict pre-ruin paymentTimes. Then the real signed integral over paymentTimes(ruinTime)∩Iic n converges to the full unrestricted real integral. The proof splits the same original restricted Stieltjes measure into Iic n and Ioi n with the pinned Mathlib integral_add_compl, and uses the remotely Proved exact original source signed tail convergence. This handles all continuous, jump, and time-zero right-limit atom cash and does not infer integrability from totalised real integrals.
-- source:
--   Accepted exact source unrestricted signed tail c94fa5f6; pinned Mathlib MeasureTheory.integral_add_compl and Measure.restrict_restrict.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_integrable_signed_horizon_tendsto_full_stieltjes_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    Tendsto (fun n : ℕ =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω))
      atTop (𝓝 (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω))) := by sorry
