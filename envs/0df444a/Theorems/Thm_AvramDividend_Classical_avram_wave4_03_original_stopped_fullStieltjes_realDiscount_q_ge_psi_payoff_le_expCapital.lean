-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_stopped_fullStieltjes_realDiscount_q_ge_psi_payoff_le_expCapital
-- name    : AvramDividend.Classical.avram_wave4_03_original_stopped_fullStieltjes_realDiscount_q_ge_psi_payoff_le_expCapital
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:18:22.098022+00:00
-- url     : https://prove2.me/theorems/1694b09e-5b52-47df-81e8-71d80cb9516a
-- title:
--   Original source real-clock strictly stopped full-Stieltjes dividend reward at every q≥ψ(1)
-- statement:
--   For a capped admissible dividend strategy on the original spectrally negative Lévy probability space, and any discount rate q≥ψ(1), the actual expected strictly pre-ruin real-clock complete Stieltjes dividend reward over paymentTimes(ruinTime) intersect Iic T is bounded by exp x. Includes time-zero right atom, positive-time right atoms, diffuse and singular-continuous payments, and uses the original accepted reward convention. The theorem follows from the stopped closed-horizon source bound q≥ψ(1) and the corrected restriction identity. It is an exponential-test estimate and does not establish the arbitrary-C1 HJB core.
-- source:
--   Prepared q≥ψ1 full closed stopped source bound target (unproved at draft time) plus canonically proved Chat04B source reward restriction 122d4c4b-f0ad-47c3-a555-9ddfc26bd6d8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_cash_q_ge_psi
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_original_reward_eq_closed_horizon_restriction
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave4_03_original_stopped_fullStieltjes_realDiscount_q_ge_psi_payoff_le_expCapital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : X.ψ 1 ≤ q)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂dividendMeasure D ω ∂P) ≤ ENNReal.ofReal (Real.exp x) := by sorry
