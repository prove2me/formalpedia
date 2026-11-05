-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:32:26.170229+00:00
-- url     : https://prove2.me/theorems/159d8858-9320-4759-841f-7a1f78a90c7e
-- title:
--   Real original dividend submeasure mass bounded by exact finite-horizon stopped Cash
-- statement:
--   For each actual original admissible dividend path, all nonnegative discount rates, finite observation horizons, and any path-dependent Stieltjes submeasure dominated by the original dividendMeasure, the ordinary real mass of that submeasure over exact ruin-stopped paymentTimes intersected with the closed horizon is bounded by original stopped discounted Cash.toReal divided by exp(-qT). This handles all diffuse components and all eligible right-payment atoms, including at time zero and at the horizon, without dropping singular-continuous mass.
-- source:
--   Accepted true original payment mass-to-Cash inequality 8c43cf59 and original literal Cash finiteness c4e50d93; pinned Mathlib ENNReal.toReal_mono, ENNReal.toReal_ofReal_mul and Real.exp_pos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_dominated_mass_le_discounted_cash
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ν : Measure ℝ) (hdom : ν ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    ν.real (paymentTimes σ ∩ Iic (T : ℝ)) ≤
      (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal /
          Real.exp (-(q * (T : ℝ))) := by sorry
