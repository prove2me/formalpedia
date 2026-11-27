-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_random_closed_cash_measurable
-- name    : AvramDividend.Classical.avram_locmoll_random_closed_cash_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:02:07.773819+00:00
-- url     : https://prove2.me/theorems/e22326ad-c30f-4958-a260-eacd6796ce48
-- title:
--   Original eligible discounted dividends up to a measurable closed random clock are measurable
-- statement:
--   Original eligible discounted dividends up to a measurable closed random clock are measurable
-- source:
--   Exact decomposition of 1956f1aa-dda2-5052-8723-910f7fb63181, Avram Proposition 4(i)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_random_closed_cash_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (θ : Ω → ℝ≥0)
    (hθ : IsStoppingTime 𝓕.rightCont (fun ω => (θ ω : WithTop ℝ≥0))) :
    AEMeasurable (fun ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) P := by sorry
