-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_nested_rectangles_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_nested_rectangles_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:31:10.239699+00:00
-- url     : https://prove2.me/theorems/d5a1173d-7d42-4031-9c6b-558524b97f91
-- title:
--   Joint rectangle and weight monotonicity of true Lévy source jump expectations
-- statement:
--   For the actual intrinsic jump measure of the source Lévy process, interval inclusion, mark inclusion and arbitrary pointwise ENNReal weight inclusion jointly imply a weighted expected-count bound. This allows predictable simple-cell refinement or localisation without any ν-rate, finiteness, independence, or replacement process.
-- source:
--   Original intrinsic jump measure; Set.Ioc interval inclusion, Set.prod_mono, measure_mono and lintegral_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_nested_rectangles_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s0 s1 t0 t1 : ℝ≥0) (hs : s0 ≤ s1) (ht : t1 ≤ t0)
    (B C : Set ℝ) (hBC : B ⊆ C)
    (H K : Ω → ℝ≥0∞) (hHK : ∀ ω, H ω ≤ K ω) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s1 t1 ×ˢ B) ∂P) ≤
    (∫⁻ ω, K ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s0 t0 ×ˢ C) ∂P) := by sorry
