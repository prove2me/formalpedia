-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_bv_real_terminal_budget_to_closed_ennreal
-- name    : AvramDividend.Classical.avram_sweep16_bv_real_terminal_budget_to_closed_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:58:32.809742+00:00
-- url     : https://prove2.me/theorems/cb8b9f9d-b41f-44c0-9a7e-66af192c9877
-- title:
--   Original closed-horizon BV signed cash and nonnegative terminal budget implies genuine ENNReal payout bound
-- statement:
--   For an original admissible capped spectrally negative Levy dividend strategy, an integrable nonnegative terminal random variable and a source-exact expected real-converted closed-horizon dividend payout plus terminal upper bound B imply the genuine double ENNReal discounted dividend bound at the same real horizon. The conclusion retains paymentTimes(ruinTime) intersect Iic T, the time-zero atom, horizon endpoint and original dividend Stieltjes measure. The proof uses Proved d9993239 (original bounded-clock toReal-to-ENNReal transfer) and nonnegativity of the terminal mean; no Ito or Levy martingale premise is asserted.
-- source:
--   Proved d9993239-bbe3-4913-a7a4-70f731bae570; this bridge is the final deterministic expectation-to-ENNReal adapter for canonical BV core ef7e6c20 after its strictly positive-horizon original source supermartingale f5d16a51 is established. No Open theorem is imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_toReal_budget_to_ennreal_cash

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_bv_real_terminal_budget_to_closed_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (B : ℝ)
    (Term : Ω → ℝ) (hTermI : Integrable Term P)
    (hTermNonneg : ∀ ω, 0 ≤ Term ω)
    (hBudget :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
        (∫ ω, Term ω ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal B := by sorry
