-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_cash_cap_support_disjoint_partition
-- name    : AvramDividend.Classical.avram_wave7_19_original_ruin_cash_cap_support_disjoint_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T20:08:42.356976+00:00
-- url     : https://prove2.me/theorems/5c7cad26-9203-45c8-a430-d8884c537cd4
-- title:
--   Exact original ruin-payment Stieltjes cash splits into full boundary-supported and complementary contributions
-- statement:
--   The exact original discounted ruin-payment dividendMeasure integral through Iic T splits additively over any measurable boundary-support set and its complement. Taking the support set to be the cap-payment times makes upper reflection Stieltjes mass an explicit term that cannot be silently discarded when interior reserve cutoffs widen. The source paymentTimes keeps t=0 even if ruinTime=0 and excludes strictly positive t=ruinTime. The proof uses source paymentTimes_measurable and the pinned Mathlib lintegral_union for a disjoint measurable partition, with no UI, no original path continuity at ruin, and no real/ENNReal measure conversion. This does not itself prove that the cap support is measurable or that interior cutoffs exhaust the complementary cash; these remain precise W7-18/W7-08 tasks.
-- source:
--   Original ruinTime, paymentTimes and dividendMeasure definitions; Proved paymentTimes_measurable 88dafb7f and pinned Mathlib MeasureTheory.lintegral_union; source-specific boundary/cap correction to W7-18 localised Ito and W7-08 finite-horizon budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_ruin_cash_cap_support_disjoint_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (boundary : Set ℝ) (hBoundary : MeasurableSet boundary) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ boundary,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) \ boundary,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
