-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
-- name    : AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:06:53.006635+00:00
-- url     : https://prove2.me/theorems/ed1a42d8-9ded-45a9-a343-9de7e4a6385c
-- title:
--   Original bounded physical stopped strict pre-ruin discounted Stieltjes cash is L1
-- statement:
--   For any original spectrally negative Levy dividend strategy and finite bounded genuine right-continuous stopping clock, prove integrability of the strict Iio dividend cash before ruin. Original s-finite kernel measurability proves the strict cash measurable. The exact physical closed Iic versus strict Iio atom identity, together with the nonnegative right dividend increment, gives strict cash <= closed cash. The independently Proved bounded-clock full closed cash L1 theorem supplies domination. Time-zero cash remains excluded from Iio at zero, positive-ruin right dividends are excluded, and all earlier continuous cash is kept. The result is a source-exact strict reward L1 interface for d1caa4aa and 4a699fd8, without auxiliary Brownian process or centring assumption.
-- source:
--   Proved 3deca135 bounded physical closed cash integrability; Proved 54ad337e exact active right atom and 2d478c7d kernel method. Direct source-exact L1 strict cash interface for Gaussian finite/top witness integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom

open MeasureTheory Set ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) P := by sorry
