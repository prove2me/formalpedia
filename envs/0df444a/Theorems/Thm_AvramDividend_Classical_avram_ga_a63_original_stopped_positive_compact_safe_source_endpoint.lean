-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a63_original_stopped_positive_compact_safe_source_endpoint
-- name    : AvramDividend.Classical.avram_ga_a63_original_stopped_positive_compact_safe_source_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:24:33.343195+00:00
-- url     : https://prove2.me/theorems/2ae15997-1c17-4f1f-8590-8e35026f5e22
-- title:
--   Every safe small-source-displacement Gaussian spatial Taylor endpoint lies in an original stopped positive compact band almost surely
-- statement:
--   For the real original Levy source X and dividend strategy D under the actual compact stopped reserve prefix, all strictly pre-stop source cell starting states and small source displacements produce later Taylor spatial endpoints in a positive enlarged compact band almost surely.
-- source:
--   Direct original b0d9951c positive-only compact safe-cell Hessian Taylor prerequisite, uses Proved ga_a47 and gledger137.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a63_original_stopped_positive_compact_safe_source_endpoint
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < ρ ω →
      |X.X t ω - X.X s ω| ≤ (1 : ℝ) / (2 * ((j : ℝ) + 1)) →
      (1 : ℝ) / (2 * ((j : ℝ) + 1)) ≤
        x + X.X t ω - rightLimit D s ω ∧
      x + X.X t ω - rightLimit D s ω ≤
        x + ((j : ℝ) + 1) + (1 : ℝ) / (2 * ((j : ℝ) + 1)) := by sorry
