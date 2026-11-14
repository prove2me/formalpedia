-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB234_original_floor_two_cutoff_shrinking_union_from_upper_null
-- name    : AvramDividend.Classical.avram_gbB234_original_floor_two_cutoff_shrinking_union_from_upper_null
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T08:22:18.016201+00:00
-- url     : https://prove2.me/theorems/f6f5666c-fac0-4f21-9a8a-f572b33c96ab
-- title:
--   Original positive floor and upper fixed-level null occupation imply vanishing two-cutoff strip occupation
-- statement:
--   In the genuine unbounded-variation zero-jump original dividend model, the strict pre-stop reserve floor eliminates the lower clipping level δ/2. If the original stochastic theorem guarantees zero occupation at the arbitrary prescribed upper level b, the measure of the union of shrinking neighbourhoods of both boundaries tends to zero almost surely. This makes B100 the only fixed-level occupation bottleneck in the two-sided clipping convergence route.
-- source:
--   Root-oriented B65 original controlled two-cutoff occupation, directly integrates B228+B100+B223 rather than requiring B100 at both prescribed levels.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB234_original_floor_two_cutoff_shrinking_union_from_upper_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          (abs (x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω - δ / 2) <
              (1 : ℝ) / ((k : ℝ) + 1) ∨
           abs (x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω - b) <
              (1 : ℝ) / ((k : ℝ) + 1))})
        atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
