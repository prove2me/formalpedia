-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_zero_horizon_exact_nu_rate
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_zero_horizon_exact_nu_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:04:21.398675+00:00
-- url     : https://prove2.me/theorems/157f228d-607a-4a90-a81f-7fab07ca6e24
-- title:
--   Exact original zero-horizon ENNReal marked rate identity including infinite ν mass
-- statement:
--   At the zero time origin and zero horizon, prove the exact source intrinsic marked count first-moment identity equals zero times the original Lévy measure of any mark B, including ν(B)=∞. Use the already Proved original pathwise zero-horizon expectation; no jump intensity, compensation, or finiteness assumptions are invoked.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_zero_horizon_vanishes

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_zero_horizon_exact_nu_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 0 ×ˢ B) ∂P) =
      (0 : ℝ≥0∞) * X.ν B := by sorry
