-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_intrinsic_integral_origin_means
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_integral_origin_means
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:20:32.724198+00:00
-- url     : https://prove2.me/theorems/144e9298-cc95-4450-9e69-245bc1b04188
-- title:
--   Genuine original countable intrinsic jump-measure integral equals weighted zero-origin means
-- statement:
--   For any countable family of genuine Lévy marked time rectangles with distinct deterministic starts and arbitrary nonnegative weights adapted at those starts, the expectation of the true source intrinsic jump-measure integral of their countable indicator sum equals the sum of each expected past weight times the corresponding original zero-origin marked count mean. This integrates the actual pathwise marked-jump measure and uses already-proved stationary source means. It does not assume or conclude the unproved original ν-rate; P2-A/P2-C/P2-D must identify it independently.
-- source:
--   Proved original intrinsic countable simple pathwise identity 2bbac71e-ddd6-42a8-afa6-810b47a061f6 and new original countable zero-origin mean helper published separately (expected after publication 973afa3d-b146-4edd-bfa2-f98956ab3a4a).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_countable_simple_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_predictable_origin_means

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_intrinsic_integral_origin_means
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i)) :
    (∫⁻ ω, (∫⁻ p, ∑' i, (Ioc (s i) (s i + T i) ×ˢ B i).indicator (fun _ => H i ω) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (T i) ×ˢ B i) ∂P) := by sorry
