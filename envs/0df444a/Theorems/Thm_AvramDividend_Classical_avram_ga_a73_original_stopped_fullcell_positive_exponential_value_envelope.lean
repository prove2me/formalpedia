-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a73_original_stopped_fullcell_positive_exponential_value_envelope
-- name    : AvramDividend.Classical.avram_ga_a73_original_stopped_fullcell_positive_exponential_value_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:37:46.156346+00:00
-- url     : https://prove2.me/theorems/e1e1399d-907d-48fc-9b15-16251c0cd29e
-- title:
--   Actual original Gaussian strictly pre-stop full-cell spatial Taylor HJB value obeys one fixed positive-halfline exponential bound
-- statement:
--   For the genuine original pure Gaussian Levy source, actual cumulative dividend strategy and positive stopped reserve prefix, all actual full spatial Taylor source endpoints before stopping have one uniform exponential upper value envelope almost surely, including the large positive source excursion events.
-- source:
--   Original b0d9951c positive-only HJB value growth at actual stopped full-cell spatial endpoints, uses Proved ga_a46 and gledger65.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a73_original_stopped_fullcell_positive_exponential_value_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        s < t → 0 < t → t < ρ ω →
        w (x + X.X t ω - rightLimit D s ω) ≤
          K * Real.exp (θ * (x + X.X t ω - rightLimit D s ω)) := by sorry
