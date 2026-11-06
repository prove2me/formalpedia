-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_immediate_ruin_clipped_closed_cash_eq_initial_atom
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_immediate_ruin_clipped_closed_cash_eq_initial_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:10:20.893206+00:00
-- url     : https://prove2.me/theorems/f3f1ae05-0766-40e9-a4ec-5290ca8768fb
-- title:
--   Exact original immediate ruin bounded-clock finite-horizon Stieltjes cash equals initial atom
-- statement:
--   If the original controlled reserve ruins immediately, the exact stopped paymentTimes(min(ruinTime,n)) weighted Stieltjes dividend mass through any nonnegative deterministic horizon is precisely the full original dividendMeasure singleton {0}, for arbitrary n, q and original X/D. This is a raw ENNReal identity retaining the full right dividend at time zero, independent of stochastic compensation, terminal values and integrability assumptions.
-- source:
--   Original paymentTimes σ = {s | 0≤s and (s=0 or ofReal s<σ)}. Immediate ruin forces min(ruinTime,n)=0; its entire paymentTimes supports only s=0, which lies in Iic T for T≥0. The source singleton weighted integral is exactly the mass of {0} by Proved 1fb597ac. No law or proxy process.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_immediate_ruin_clipped_closed_cash_eq_initial_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) (ω : Ω)
    (hRuinZero : ruinTime X x D ω = 0) :
    (∫⁻ s in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
    (dividendMeasure D ω) ({0} : Set ℝ) := by sorry
