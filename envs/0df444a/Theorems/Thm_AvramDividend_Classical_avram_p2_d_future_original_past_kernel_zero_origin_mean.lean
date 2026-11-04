-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_past_kernel_zero_origin_mean
-- name    : AvramDividend.Classical.avram_p2_d_future_original_past_kernel_zero_origin_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:41:28.039648+00:00
-- url     : https://prove2.me/theorems/aa898276-26cf-48f7-b3e5-d1c2b036c7bf
-- title:
--   Measurable original future marked count has stationary past-event kernel at every real horizon
-- statement:
--   For every original Lévy interval (s,t] and arbitrary Borel marks, construct one measurable functional of the exact shifted original future increment path, equal pointwise to the literal marked jump count, such that integrating it against any event measurable at s factors as P(A) times the original zero-origin count mean on (0,t-s]. This is the source-complete conditional future-kernel theorem with the separate ν identification still explicit.
-- source:
--   Apply Proved original future extractor 5cf3e058, Proved original future/past factorisation ad24b83b, and Proved stationary original count mean add050a6. Transport s+(t-s)=t. This owns no P2-E theorem and uses no assumed ν-rate.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_original_past_kernel_zero_origin_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ∧
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) ∂P) =
          P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (t - s) ×ˢ B) ∂P) := by sorry
