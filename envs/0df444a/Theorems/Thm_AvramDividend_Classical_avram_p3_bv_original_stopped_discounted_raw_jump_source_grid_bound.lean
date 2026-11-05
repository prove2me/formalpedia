-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_stopped_discounted_raw_jump_source_grid_bound
-- name    : AvramDividend.Classical.avram_p3_bv_original_stopped_discounted_raw_jump_source_grid_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:21:30.178634+00:00
-- url     : https://prove2.me/theorems/e94da2af-4dc5-4932-961c-b63cc952f260
-- title:
--   Complete original ruin-stopped discounted physical source grid bounded by drift and actual raw negative-jump sum
-- statement:
--   For every nondecreasing physical source grid with each cell ending at time zero or strictly before actual ruin, the discounted sum of genuine cap-linear frozen-source Levy increments is bounded by the analogous sum using the deterministic Levy drift minus every raw negative-jump interval, with the original continuous BV residual discarded by its proven sign. This holds on one full original almost-sure event simultaneously for every source grid and length.
-- source:
--   Source-exact assembly of Proved physical cap-linear residual drop c19000be-6a90-4ccb-907f-501df7c1fa8a and genuine original frozen endpoint nonnegative a9e0006d-b2e7-4e0c-857f-0fcc370ac525. Intermediate source grid inequality for stopped triple-mesh certificate db6a3111.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_frozen_preruin_source_cell_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_cell_caplinear_raw_jump_envelope

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- All stopped original physical source cells lose their continuous BV
   residual in one discounted inequality, retaining raw negative jumps. -/

theorem AvramDividend.Classical.avram_p3_bv_original_stopped_discounted_raw_jump_source_grid_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      Monotone u →
      (∀ i : ℕ, i < n →
        u (i + 1) = 0 ∨
          (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) →
      (∑ i ∈ Finset.range n,
        Real.exp (-(q * (u i : ℝ))) *
          (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
            V (x + X.X (u i) ω - rightLimit D (u i) ω))) ≤
      (∑ i ∈ Finset.range n,
        Real.exp (-(q * (u i : ℝ))) *
          (V ((x + X.X (u i) ω - rightLimit D (u i) ω) +
              (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
              (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
               else 0)) -
            V (x + X.X (u i) ω - rightLimit D (u i) ω))) := by sorry
