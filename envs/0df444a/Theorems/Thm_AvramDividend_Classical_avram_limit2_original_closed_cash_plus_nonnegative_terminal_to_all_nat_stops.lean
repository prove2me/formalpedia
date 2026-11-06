-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_closed_cash_plus_nonnegative_terminal_to_all_nat_stops
-- name    : AvramDividend.Classical.avram_limit2_original_closed_cash_plus_nonnegative_terminal_to_all_nat_stops
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:46:41.178861+00:00
-- url     : https://prove2.me/theorems/00a10de3-b78e-4bc4-b243-86842a62ab09
-- title:
--   Original closed-horizon expected Stieltjes cash plus arbitrary nonnegative terminal budget implies every natural ruin-stopped cash bound
-- statement:
--   Under genuine original X, q, x and dividendMeasure D, any uniform expected closed-horizon discounted cash-plus-nonnegative-terminal budget yields the uniform natural ruin-stopped expected cash estimate at every integer n, including 0. First bound stopped cash by raw closed cash at real T=n using Proved/public 4eb76074; then use lintegral_mono to retain a nonnegative terminal term and the given budget. The proof preserves original ruin stop, time-zero/right-horizon atoms, uses only ENNReal arithmetic and natural real-clock casting, and does not assert terminal vanishing or substitute an equality-in-law. This is independent support for the P3/P4 positive terminal finite-horizon cash budget to Sweep16 natural value route. Its parent bridge remains to be imported by canonical owner.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_real_stopped_cash_le_closed_horizon_cash
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_closed_cash_plus_nonnegative_terminal_to_all_nat_stops
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (Terminal : ℝ → Ω → ℝ≥0∞)
    (hBudget : ∀ (T : ℝ) (hT : 0 ≤ T),
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal T ω) ∂P) ≤ B) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B := by sorry
