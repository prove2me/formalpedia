-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_natural_cash_saturates_any_later_closed_horizon
-- name    : AvramDividend.Classical.avram_limit2_original_natural_cash_saturates_any_later_closed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:16:42.119332+00:00
-- url     : https://prove2.me/theorems/ff8ef70e-cbf0-491d-91db-ce7a8906ebcd
-- title:
--   Genuine natural ruin-stopped expected cash saturates every later closed real horizon including zero
-- statement:
--   For genuine original discounted dividendMeasure stopped at min(ruinTime,n), the unmasked expected Stieltjes cash equals the same expected integral restricted to Iic T whenever real n≤T, including n=0. Unlike the earlier positive-n source lemma a9633c0c this handles the time-zero clock directly. Use public Proved natural stopped paymentTimes subset Iic n 0482c9a7 fibrewise, transitivity to Iic T and rewrite nested lintegrals. This identifies exactly the strict/closed source cash needed for later-horizon HJB budget integration.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_stopped_paymentTimes_subset_closed_nat_clock
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_natural_cash_saturates_any_later_closed_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (T : ℝ)
    (hTn : (n : ℝ) ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Set.Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by sorry
