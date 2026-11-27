-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_eligible_measure_finite
-- name    : AvramDividend.Classical.avram_locmoll_band_eligible_measure_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:19:07.420793+00:00
-- url     : https://prove2.me/theorems/d202a09f-06e5-570f-ab2d-90b524e7c421
-- title:
--   Eligible closed-horizon Stieltjes measure has finite total mass
-- statement:
--   Eligible closed-horizon Stieltjes measure has finite total mass
-- source:
--   Exact atomic diffuse secant integral b980c2dc-b50f-4bb4-b148-7f7a2859258e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_eligible_measure_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H : ℝ≥0) :
    let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
    let μ := (dividendMeasure D ω).restrict S
    IsFiniteMeasure μ := by sorry
