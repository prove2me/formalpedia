-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a190_original_stopped_source_small_raw_C2_Taylor_cell_modulus
-- name    : AvramDividend.Classical.avram_ga_a190_original_stopped_source_small_raw_C2_Taylor_cell_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:02:22.035378+00:00
-- url     : https://prove2.me/theorems/21fda819-8730-4eba-b0c4-86dc810b05c8
-- title:
--   Original stopped Gaussian physical source individual small-increment Taylor remainder is uniformly quadratic with arbitrarily small coefficient
-- statement:
--   For the genuine spectrally negative Lévy source X, dividend right limits and a compact positive postpayment prefix before an arbitrary stopping clock, smoothness of w implies that for every small error tolerance there is a deterministic raw increment threshold such that the absolute second-order classical Taylor remainder at each stopped source cell is bounded by the tolerance times the squared raw increment. Reuses the Proved original stopped finite-cell classical modulus a76 on a singleton and the Proved postpayment compact prefix gledger137. This is the essential small-source estimate for the true full-cell positive Taylor L1 goal a149.
-- source:
--   Proved ga_a76 original stopped safe small source Taylor modulus and gledger137 original right-limit compact prefix band.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a76_original_stopped_safe_small_source_classical_Taylor_modulus
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a190_original_stopped_source_small_raw_C2_Taylor_cell_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hTopCap : C = ⊤) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < ρ ω →
        |X.X t ω - X.X s ω| < δ →
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        let r : ℝ := X.X t ω - X.X s ω
        |w (y + r) - w y - deriv w y * r -
          (iteratedDeriv 2 w y * r^2) / 2| ≤ ε * r^2 := by sorry
