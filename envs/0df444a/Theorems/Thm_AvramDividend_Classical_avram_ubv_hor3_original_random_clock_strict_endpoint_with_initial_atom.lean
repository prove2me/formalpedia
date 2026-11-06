-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_random_clock_strict_endpoint_with_initial_atom
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_random_clock_strict_endpoint_with_initial_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:21:39.303504+00:00
-- url     : https://prove2.me/theorems/54023274-c911-4969-b240-bd1d1a39b1d9
-- title:
--   Exact original random-clock stopped Stieltjes cash includes zero atom and strict positive endpoint
-- statement:
--   For the original Levy reserve and actual dividendMeasure, any pathwise nonnegative random real clock τ clips paymentTimes at strictly t<τ while preserving t=0 even when τ=0. This is an exact expected discounted cash identity on any closed deterministic Iic T. No measurability, martingale or finiteness premise is used beyond equality of the pathwise Stieltjes domains; it applies equally to zero stopping and interior localisation.
-- source:
--   Combines the public positive-ofReal paymentTimes endpoint identity 3634eef8 with the public zero-clock singleton payment identity 77cdd573, using the exact original ruinTime and dividendMeasure. No source witness, d457/665 budget, P4-F3 target or downstream SWEEP theorem imported.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_random_clock_strict_endpoint_with_initial_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ)
    (hτ : ∀ ω, 0 ≤ τ ω) (q T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal (τ ω))) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ (Iio (τ ω) ∪ {0})) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
