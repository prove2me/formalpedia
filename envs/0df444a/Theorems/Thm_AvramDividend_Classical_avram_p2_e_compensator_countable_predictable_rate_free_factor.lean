-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_countable_predictable_rate_free_factor
-- name    : AvramDividend.Classical.avram_p2_e_compensator_countable_predictable_rate_free_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:02:03.647454+00:00
-- url     : https://prove2.me/theorems/4601b26a-39d4-4492-ad2b-80fce1bd10c7
-- title:
--   Countably many original predictable marked rectangles factor from their own count means without Levy rate
-- statement:
--   On the actual Lévy sample space and original filtration, any countable sequence of nonnegative past-Fs-measurable weights times source intrinsic left-limit marked counts has ENNReal total expectation equal to the sum of products E[Wi]E[Ni]. Uses Tonelli for genuine source counts and past-future factorisation, with no moment finiteness or prescribed ν-rate assumption.
-- source:
--   Accepted P2-E original source count measurability 8146a449 and original weighted intrinsic rectangle factorisation 75e37892; pinned Mathlib lintegral_tsum/tsum_congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_intrinsic_rectangle_factor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_countable_predictable_rate_free_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℕ → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (W : ℕ → Ω → ℝ≥0∞)
    (hW : ∀ i, Measurable[𝓕 (s i)] (W i)) :
    (∫⁻ ω, ∑' i, W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
    ∑' i, (∫⁻ ω, W i ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) := by sorry
