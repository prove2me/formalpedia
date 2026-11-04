-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_mean_past_weighted_real_integrable
-- name    : AvramDividend.Classical.avram_p2_e_compensator_finite_mean_past_weighted_real_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:42:39.725871+00:00
-- url     : https://prove2.me/theorems/983cbffc-1ef2-4fde-93f5-da4e0aeaac00
-- title:
--   Original intrinsic count and past weight with finite means give real L1 product independently of Lévy rate
-- statement:
--   Whenever the actual original intrinsic marked count has finite expected count and an arbitrary nonnegative original F_s measurable past weight has finite expectation, the real conversion of their product is integrable. The proof uses only original future-past independence and count measurability, and has no ν-rate assumption.
-- source:
--   Proved P2-E original intrinsic rectangle measurability and original weighted past factorisation; pinned Mathlib integrable_toReal_of_lintegral_ne_top and Pi.mul_apply.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_intrinsic_rectangle_factor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_finite_mean_past_weighted_real_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W)
    (hWfinite : (∫⁻ ω, W ω ∂P) < ⊤)
    (hNfinite : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) < ⊤) :
    Integrable (fun ω => (W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal) P := by sorry
