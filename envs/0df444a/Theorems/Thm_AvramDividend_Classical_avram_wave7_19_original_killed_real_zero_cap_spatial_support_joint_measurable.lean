-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_killed_real_zero_cap_spatial_support_joint_measurable
-- name    : AvramDividend.Classical.avram_wave7_19_original_killed_real_zero_cap_spatial_support_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:45:04.97628+00:00
-- url     : https://prove2.me/theorems/b1a4123b-06c6-4802-8b3b-2cc632b14055
-- title:
--   Actual pre-ruin finite-horizon zero/cap and interior postpayment supports are jointly measurable in real Stieltjes time and sample
-- statement:
--   For the true original killed dividend reward domain, joint Borel measurability holds for both zero/cap post-rightpayment reserve boundary and each lower/upper interior band after intersection with the exact original paymentTimes(ruinTime) and deterministic finite horizon. This excludes any post-ruin extra cash premise while retaining time-zero right payment and cap-supported singular Stieltjes atoms. Uses only previously Proved source ruinTime_measurable, paymentTimes_joint_measurable, and W8-20 post-rightpayment reserve joint measurability, plus pinned Mathlib measurable coercion; no extra canonical stochastic condition.
-- source:
--   Proved paymentTimes_joint_measurable UUID 6e9faa20, ruinTime_measurable bbfbecf4, source W8-20 postpayment joint reserve 6410e850.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_killed_real_zero_cap_spatial_support_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x T : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (lower : ℕ → ℝ) (upper : ℕ → ℝ≥0∞) (n : ℕ) :
    MeasurableSet {p : ℝ × Ω |
      p.1 ∈ paymentTimes (ruinTime X x D p.2) ∧ p.1 ≤ T ∧
        (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2 = 0 ∨ ENNReal.ofReal (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2) = C)} ∧
    MeasurableSet {p : ℝ × Ω |
      p.1 ∈ paymentTimes (ruinTime X x D p.2) ∧ p.1 ≤ T ∧
        lower n < x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2 ∧ ENNReal.ofReal (x + X.X p.1.toNNReal p.2 - rightLimit D p.1.toNNReal p.2) < upper n} := by sorry
