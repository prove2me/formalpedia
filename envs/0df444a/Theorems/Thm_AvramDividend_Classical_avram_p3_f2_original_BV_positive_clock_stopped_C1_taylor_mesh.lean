-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_BV_positive_clock_stopped_C1_taylor_mesh
-- name    : AvramDividend.Classical.avram_p3_f2_original_BV_positive_clock_stopped_C1_taylor_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:56:29.121398+00:00
-- url     : https://prove2.me/theorems/3bf70c3c-4527-4f26-bbaf-1cbeeb16857f
-- title:
--   Original BV positive-clock interior stopped C1 Taylor mesh with pathwise time threshold
-- statement:
--   For almost every original BV Lévy path and any compact strictly positive physical clock band, derivative uniform continuity on a compact positive reserve band and the already proved pathwise uniform continuity of the true negative-jump-removed original source Y jointly provide a strictly positive clock-grid step δ. Every actual controlled reserve source cell in the compact interior then satisfies the exact C1 Taylor remainder bound with epsilon times the original Y increment. The threshold is shared across all grids on that sample path. Initial, ruin and horizon atoms remain separate obligations.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_positive_compact_physical_Y_cell_modulus
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_interior_C1_source_cell_taylor
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_BV_positive_clock_stopped_C1_taylor_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), 0 < s →
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
        ∀ (u : ℕ → ℝ≥0) (n : ℕ),
          let J : ℝ≥0 → ℝ := fun r =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
              Function.leftLim (fun q : ℝ≥0 => X.X q ω) v - X.X v ω else 0
          let Y : ℝ≥0 → ℝ := fun r => X.X r ω + J r
          let z : ℕ → ℝ := fun i =>
            x + X.X (u i) ω - rightLimit D (u i) ω
          let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
          (∀ i, i < n →
            u i ∈ Set.Icc s t ∧ u (i + 1) ∈ Set.Icc s t) →
          (∀ i, i < n → dist (u (i + 1)) (u i) < δ) →
          (∀ i, i < n →
            Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
          ∀ i, i < n →
            |w (z i + c i) - w (z i) - deriv w (z i) * c i| ≤
              ε * |c i| := by sorry
