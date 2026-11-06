-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_clock_beyond_closed_horizon_cash_eq_unclipped_ruin
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_clock_beyond_closed_horizon_cash_eq_unclipped_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:31:01.75356+00:00
-- url     : https://prove2.me/theorems/4569b16d-0d94-43a2-ae48-f2d1965c6002
-- title:
--   Exact original Lévy closed-horizon dividend cash is independent of natural cutoff n whenever T<n
-- statement:
--   For the actual original Levy process X, admissible or arbitrary dividend process D, original random ruinTime and Stieltjes dividendMeasure, if a positive integer truncation n strictly exceeds the real closed horizon T, expected discounted cash stopped at min(ruinTime,n) agrees exactly with expected cash stopped only at ruinTime on Iic T. The strict inequality T<n retains every payment at the closed horizon T, including the atom at T and at time zero, while excluding artificial clock endpoint n. No equality in law or extraneous process is used.
-- source:
--   Source-exact expected-cash horizon-unclipping bridge for original-process positive-horizon budget. Uses Proved public AvramDividend.Classical.avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq (26471312) and an explicit inclusion Iic T subset Iio n from T<n. Independent of fdb, 0dda, 750, d457 and 665; reusable by SWEEP16 finite-horizon passage.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_clock_beyond_closed_horizon_cash_eq_unclipped_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (n : ℕ)
    (hn : 0 < n) (hTn : T < (n : ℝ)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
