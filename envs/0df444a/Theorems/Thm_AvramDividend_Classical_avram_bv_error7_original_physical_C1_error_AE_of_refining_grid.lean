-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_physical_C1_error_AE_of_refining_grid
-- name    : AvramDividend.Classical.avram_bv_error7_original_physical_C1_error_AE_of_refining_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:27:36.310195+00:00
-- url     : https://prove2.me/theorems/abd83bb1-62c6-4e4f-bc22-b0a718e2e13c
-- title:
--   Actual original BV stopped physical C1 error tends to zero almost surely on refining compact interior grids
-- statement:
--   Under the actual original spectrally negative BV Lévy process X and admissible dividend strategy D, consider genuine monotone physical grids from zero to T and the exact discounted C1 Taylor source commutators of Y=X plus original negative-jump sum. If almost surely all pre-right-payment reserve cell segments stay in a fixed compact interior subcap band and the largest original Y increment on the grid tends to zero, then these real-valued Taylor error variables tend to zero almost surely. The result is the exact original stochastic adapter of the already Proved physical mesh error theorem 46049abe, with no expectations, budgets, or surrogate process.
-- source:
--   Exact Proved original physical mesh C1 error convergence 46049abe-2c3f-43ea-855e-ffc52dcf0b42. Intended to discharge the hErrAE premise of the original BV-ERROR7 positive-error dominated-convergence theorem 70a2660b-af9a-4e0c-9e31-a0cf5eed04e9 and uniform physical Taylor adapter. The band/refinement hypotheses are genuine stopped process obligations, not inferred from budgets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_BV_physical_mesh_errors_vanish
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_physical_C1_error_AE_of_refining_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
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
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hGrid : ∀ m, u m 0 = 0 ∧ u m (k m) = T ∧
      (∀ i, i < k m → u m i ≤ u m (i + 1)))
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       ∑ i ∈ Finset.range (k m),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (hPath : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m (i + 1)) - Y (u m i)
       (∀ m i, i < k m →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m → |c m i| < δ))) :
    ∀ᵐ ω ∂P, Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)) := by sorry
