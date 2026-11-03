-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
-- name    : AvramDividend.Classical.avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:27:22.55321+00:00
-- url     : https://prove2.me/theorems/cabfeef5-97ba-4487-b258-efc0813afa48
-- title:
--   Pathwise exact original full ruin-stopped Stieltjes same-measure real/ENNReal equality on real horizon
-- statement:
--   At every original sample omega and real finite T>=0, the discounted ENNReal Stieltjes dividend cash through the actual ruin-stopped paymentTimes cap Iic T equals ENNReal.ofReal of the signed real Stieltjes integral against the identical original dividendMeasure on the identical stopped domain, for q>=0. Only IsDividendStrategy is required; no capped admissibility, BV/UBV, or probabilistic integrability assumption. Finite mass follows from the accepted rightLimit closed interval measure formula and all zero, jump and continuous cash are retained.
-- source:
--   Accepted W7-03 unconditional pathwise finite-NNReal-horizon exact bridge a5c80ef7, Real.coe_toNNReal T hT.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ENNReal.ofReal
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
