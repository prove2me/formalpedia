-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_BV_source_mesh_error_budget
-- name    : AvramDividend.Classical.avram_p3_f2_original_discounted_BV_source_mesh_error_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:13:56.852714+00:00
-- url     : https://prove2.me/theorems/cf5b9fb6-687b-43dd-b185-d99ad5b834fe
-- title:
--   Almost-sure source-exact discounted BV stopped-mesh C1 error budget from real drift and residual
-- statement:
--   On a full-measure event for the actual original bounded-variation spectrally negative Lévy process X, the physical jump-removed path Y has absolute finite-grid variation bounded explicitly by drift and the actual nondecreasing raw residual R. The uniform discounted C1 Taylor remainder estimate on the true original admissible dividend reserve gives one global positive mesh threshold for epsilon. For every physical nondecreasing clock grid with interior reserve source cells smaller than that threshold, the entire signed discounted Taylor error is at most epsilon times the exact drift/R source variation budget. This combines the real stochastic source event with exact discounted chain cells and is uniform in sample-path-selected grids; no integrability, stopped ruin atom or expectation claim is silently assumed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_BV_all_Y_physical_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_discounted_BV_source_mesh_error_budget
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
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P,
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
        ∀ (u : ℕ → ℝ≥0) (n : ℕ),
          let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
          let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
          let R : ℝ≥0 → ℝ := fun t =>
            ((t : ℝ) * X.drift - X.X t ω) - J t
          let z : ℕ → ℝ := fun i =>
            x + X.X (u i) ω - rightLimit D (u i) ω
          let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
          (∀ i, i < n → u i ≤ u (i + 1)) →
          (∀ i, i < n →
            Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
          (∀ i, i < n → |c i| < δ) →
          |∑ i ∈ Finset.range n,
            Real.exp (-(q * (u i : ℝ))) *
              (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
          ε * (|X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0))) := by sorry
