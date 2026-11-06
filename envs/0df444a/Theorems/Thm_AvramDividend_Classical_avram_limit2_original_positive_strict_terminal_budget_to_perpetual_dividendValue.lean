-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_strict_terminal_budget_to_perpetual_dividendValue
-- name    : AvramDividend.Classical.avram_limit2_original_positive_strict_terminal_budget_to_perpetual_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:02:07.817124+00:00
-- url     : https://prove2.me/theorems/ffc75253-331c-43cb-ae18-8e21dbfdceff
-- title:
--   Positive strict original dividend cash and nonnegative terminal budgets imply the actual perpetual dividendValue bound
-- statement:
--   For the original spectrally negative Lévy process X and an actual IsAdmissible dividend regulator D, a uniform expected strictly-positive Iio horizon discounted Stieltjes cash plus arbitrary nonnegative terminal bound implies the real infinite-horizon dividendValue X q x D ≤ B. The source-exact bridge uses the public strict cash-to-all-natural-stops adapter and the Proved original natural stopped budget-to-full-value monotone convergence theorem a28c3854. Positive real right-horizon cash, ruin stopping and the time-zero dividend are preserved. No terminal vanishing, omitted initial atom, equality-in-law or circular use of the target.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_positive_terminal_budget_to_every_nat_stop
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_positive_strict_terminal_budget_to_perpetual_dividendValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (Terminal : ℝ → Ω → ℝ≥0∞)
    (hPositive : ∀ (T : ℝ), 0 < T →
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal T ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B := by sorry
