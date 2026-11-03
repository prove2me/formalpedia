-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
-- name    : AvramDividend.Classical.avram_wave8_20_original_postpayment_reserve_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:14:57.883882+00:00
-- url     : https://prove2.me/theorems/6410e850-f445-4b5a-bc30-fd4d52ab4890
-- title:
--   Original controlled post-rightpayment reserve is jointly measurable in physical time and sample
-- statement:
--   The genuine postpayment reserve as a two-variable map of time and sample is measurable. Consequently evaluation at a merely measurable random clock is measurable, even if the clock is not a stopping time. This enables W8-20's deterministic BV terminal bound to supply non-circular integrability for arbitrary bounded measurable localisation clocks.
-- source:
--   Original source controlled Levy and dividend model. An accepted theorem 30c00aaa proves joint measurability of exp(theta*(x+X_t-D_t+) - q*t). Setting theta=1,q=0 and applying the measurable logarithm gives direct original-source jointly measurable reserve. This premise is independent of stopping, HJB, generator and stochastic supermartingale bounds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_postpayment_reserve_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      x + X.X z.1 z.2 - rightLimit D z.1 z.2) := by sorry
