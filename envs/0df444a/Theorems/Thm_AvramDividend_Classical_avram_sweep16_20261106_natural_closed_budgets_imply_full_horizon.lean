-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_natural_closed_budgets_imply_full_horizon
-- name    : AvramDividend.Classical.avram_sweep16_20261106_natural_closed_budgets_imply_full_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:39:32.951234+00:00
-- url     : https://prove2.me/theorems/ec080252-88f1-48aa-86a4-b3ff931df1fa
-- title:
--   Uniform natural stopped-ruin closed-cash budgets imply the full original ruin-horizon dividend bound
-- statement:
--   For an unchanged original spectrally negative Lévy process and dividend strategy, a uniform bound on genuine natural stopped-ruin closed-clock Stieltjes cash at each positive natural n implies the complete original ruin-clock cash bound at any real horizon T. The proof transports strict clipped payment times into the natural closed clock using a source-faithful set inclusion, then invokes the already Proved universal natural-clock to full-ruin Fatou/horizon bridge.
-- source:
--   Integration reducer for corrected UBV 429e17ca, downstream 750ad13b, and the source-faithful natural localised Ito budget 3b8e6210. Child avram_sweep16_20261106_strict_clipped_cash_le_natural_closed and Proved 196220b2 establish the exact shift. There is no surrogate physical process, no omitted time-zero cash, and no unjustified local-martingale expectation hypothesis. It is conditional only on explicit natural stopped cash budgets which remain to be established through genuine signed source witnesses.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_20261106_natural_closed_budgets_imply_full_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (budget : ℝ≥0∞)
    (hNatural : ∀ (n : ℕ), 0 < n →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget := by sorry
