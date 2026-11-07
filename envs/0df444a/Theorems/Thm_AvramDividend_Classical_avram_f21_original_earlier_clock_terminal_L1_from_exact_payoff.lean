-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f21_original_earlier_clock_terminal_L1_from_exact_payoff
-- name    : AvramDividend.Classical.avram_f21_original_earlier_clock_terminal_L1_from_exact_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:32:41.576836+00:00
-- url     : https://prove2.me/theorems/19ad7188-06ed-4e3d-a6d2-d1fac5dd710e
-- title:
--   Original earlier stopped clock: terminal L1 follows from exact reward L1 and closed Stieltjes cash
-- statement:
--   For the true capped spectrally negative Levy surplus and admissible dividend strategy, every measurable clock sigma dominated by tau has L1 discounted terminal value whenever its actual terminal-plus-discounted-closed-Stieltjes-cash reward is L1 and cash at tau is L1. This separates endpoint-correct cash integrability from the Gaussian and jump source proofs.
-- source:
--   Source-exact compact-clock integrability interface for arbitrary stopped Ito-Meyer witnesses; original ruinTime, right dividend measure, inclusive Iic endpoint.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_ordered_clocks_closed_cash_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_f21_original_earlier_clock_terminal_L1_from_exact_payoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ τ : Ω → ℝ≥0) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσmeas : Measurable (fun ω => (σ ω : ℝ)))
    (hCashτI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (Term F : Ω → ℝ)
    (hF : ∀ ω, F ω = Term ω +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P) :
    Integrable Term P := by sorry
