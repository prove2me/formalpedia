-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_strict_terminal_budgets_imply_closed_terminal_budgets
-- name    : AvramDividend.Classical.avram_limit2_strict_terminal_budgets_imply_closed_terminal_budgets
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:18:15.387343+00:00
-- url     : https://prove2.me/theorems/d1259913-707f-46de-b972-0595159453de
-- title:
--   Original strict next-horizon cash plus terminal budgets imply closed current-horizon budgets with the same terminal
-- statement:
--   The original positive discounted Stieltjes payout on paymentTimes (ruinTime X x D ω) ∩ Iic n is no larger than that on the strict next horizon Iio (n+1). The original dividend at n, including any atom at n, lies inside both domains. For each n take exactly the nonnegative terminal witness supplied by the strict budget and retain it unchanged. Use Mathlib lintegral_mono_set pathwise, add_le_add_right for that same Terminal ω, and lintegral_mono for the outer probability law. This yields a source-exact closed-horizon expected cash-plus-terminal budget without discarding horizon atoms, assuming a terminal limit, changing stopping clocks, or invoking equality-in-law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_strict_terminal_budgets_imply_closed_terminal_budgets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (hStrict : ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B) :
    ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B := by sorry
