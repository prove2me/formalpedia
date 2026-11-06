-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_strict_terminal_to_real_perpetual_L1_exact
-- name    : AvramDividend.Classical.avram_limit2_original_positive_strict_terminal_to_real_perpetual_L1_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:07:53.305146+00:00
-- url     : https://prove2.me/theorems/7bb12111-544a-471a-a8d5-5638aeb32bfc
-- title:
--   Original positive strict cash-plus-terminal source bound gives finite real perpetual Stieltjes L1 and exact dividendValue mean
-- statement:
--   For an actual original admissible dividend strategy X x D and a finite ENNReal budget B, uniform positive strict Iio real horizon expected discounted Stieltjes cash plus arbitrary nonnegative terminal budgets imply the complete infinite-horizon original real signed Stieltjes payout is integrable in L1(P), its expected signed real payout equals the ENNReal dividendValue via ofReal exactly, and the dividendValue is bounded by B. The first bound comes from accepted/public strict positive cash+terminal to genuine dividendValue, finiteness from B<⊤, and the accepted Wave7-03 original perpetual signed Stieltjes L1 exact-mean theorem 9806569f. Zero/horizon atoms and actual ruin stopping remain unchanged; no terminal vanishing or equality-in-law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_strict_terminal_budget_to_perpetual_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_positive_strict_terminal_to_real_perpetual_L1_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (Terminal : ℝ → Ω → ℝ≥0∞)
    (hPositive : ∀ (T : ℝ), 0 < T →
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal T ω) ∂P) ≤ B) :
    (Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)) ∧
    dividendValue X q x D ≤ B := by sorry
