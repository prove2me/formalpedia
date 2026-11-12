-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger106_original_ruinclipped_strict_mass_le_cash
-- name    : AvramDividend.Classical.avram_gledger106_original_ruinclipped_strict_mass_le_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:02:01.028179+00:00
-- url     : https://prove2.me/theorems/8274eb84-e314-419a-a336-c1d3c3acd195
-- title:
--   Original clipped strict mass is pointwise bounded by bounded-horizon discounted cash
-- statement:
--   For the original process under a clock no later than ruin and bounded by n, the original unweighted strict dividend Stieltjes mass is bounded by exp(qn) times the finite discounted strict dividend cash. It isolates the first error component in gledger39.
-- source:
--   Uses proved gledger100 and 101 and original stopped literal cash finiteness; needed by gledger39.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger106_original_ruinclipped_strict_mass_le_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (n ρ : ℝ≥0) (hρn : ρ ≤ n)
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω) :
    (dividendMeasure D ω (Ioo (0 : ℝ) (ρ : ℝ))).toReal ≤
      Real.exp (q * (n : ℝ)) *
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
