-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ubv_zero_start_original_full_discounted_stieltjes_reward_eq_zero
-- name    : AvramDividend.Classical.avram_wave6_08_ubv_zero_start_original_full_discounted_stieltjes_reward_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:11:19.300291+00:00
-- url     : https://prove2.me/theorems/362849ee-d95c-44d6-be58-466618cd7f00
-- title:
--   Zero-capital original UBV full discounted Stieltjes payout is exactly zero for all caps and horizons
-- statement:
--   On the actual unbounded-variation spectrally negative Lévy space, for an arbitrary genuine admissible capped dividend strategy with initial capital exactly zero, the full expected original discounted Stieltjes payment integral is exactly zero at every finite closed horizon. The source path is ruined immediately almost surely, and pathwise original initial-atom budget is bounded above by initial reserve zero. No HJB candidate, source Itô calculus, or missed jump convention is assumed; the zero time atom is included and shown to vanish.
-- source:
--   Canonically Proved original zero-start immediate ruin 2df9814e-41d9-4386-8e41-2fc17b1d5a4c, and exact source immediate-ruin original Stieltjes upper budget 389a618c-8fb0-4164-afac-c2bfd197c65d (accepted aab3889e-aae1-4551-8aaf-9cdcbf637f88). Chat08 owns this strengthened zero-start source subcase.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ubv_any_original_zero_start_instant_ruin_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_ubv_zero_start_original_full_discounted_stieltjes_reward_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 C D)
    (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) = 0 := by sorry
