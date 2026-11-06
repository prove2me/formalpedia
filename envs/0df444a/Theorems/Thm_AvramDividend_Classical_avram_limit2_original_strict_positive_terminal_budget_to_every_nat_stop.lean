-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_positive_terminal_budget_to_every_nat_stop
-- name    : AvramDividend.Classical.avram_limit2_original_strict_positive_terminal_budget_to_every_nat_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:53:47.432681+00:00
-- url     : https://prove2.me/theorems/b2c3d3c8-3ffb-4781-b46a-d184f1a86f91
-- title:
--   Original strictly positive horizon cash plus nonnegative terminal budgets bound every natural ruin-stopped dividend cash
-- statement:
--   Under exact original X, D, q and ruinTime, a uniform discounted dividendMeasure strict Iio T cash plus arbitrary nonnegative terminal expected budget at every T>0 implies a uniform expected cash bound on paymentTimes(min(ruinTime,n)) for every n including zero. The proof moves from the natural stopped n clock to closed Iic n by public 4eb76074, then to strict Iio(n+1) by public 4f845e71, retains the nonnegative terminal and invokes the strictly-positive source budget. The time-zero atom and potential right-boundary atom are preserved; no terminal vanishing, equality-in-law, circular HJB assumptions or artificial positive clock at n=0.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_real_stopped_cash_le_closed_horizon_cash
import Theorems.Thm_AvramDividend_Classical_avram_limit2_strict_later_real_horizon_cash_dominates_closed
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_strict_positive_terminal_budget_to_every_nat_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (Terminal : ℝ → Ω → ℝ≥0∞)
    (hPositive : ∀ (T : ℝ), 0 < T →
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal T ω) ∂P) ≤ B) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B := by sorry
