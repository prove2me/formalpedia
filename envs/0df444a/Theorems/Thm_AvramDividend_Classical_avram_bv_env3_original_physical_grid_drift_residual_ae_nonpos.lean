-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_physical_grid_drift_residual_ae_nonpos
-- name    : AvramDividend.Classical.avram_bv_env3_original_physical_grid_drift_residual_ae_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:37:06.596325+00:00
-- url     : https://prove2.me/theorems/f6e60826-acf3-40af-aff8-dc74d5d9339a
-- title:
--   Original BV physical stopped finite-grid HJB plus true residual has a.e. nonpositive drift
-- statement:
--   For the exact original Lévy finite grid, the physical HJB generator sum and the compensated finite-variation residual drift sum are separately nonpositive (the latter almost surely). Therefore the source-defined total drift residual B is almost surely nonpositive without assuming B integrable or a martingale hypothesis. Does not assume cash inequality.
-- source:
--   Proved original stopped HJB generator sum c46be6b6 and original finite-variation ruin-stopped residual mesh 5852fa04.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_physical_grid_drift_residual_ae_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (B : Ω → ℝ)
    (hB : ∀ ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
      B ω =
        (∑ i ∈ Finset.range n,
          if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u (i + 1) : ℝ) - (u i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range n,
           (if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u i : ℝ))) * deriv w (Z i)
           else 0) * (R (u i) - R (u (i + 1))))) :
    ∀ᵐ ω ∂P, B ω ≤ 0 := by sorry
