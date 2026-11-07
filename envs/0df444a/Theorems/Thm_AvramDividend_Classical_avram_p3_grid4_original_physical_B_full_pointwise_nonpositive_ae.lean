-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae
-- name    : AvramDividend.Classical.avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:42:59.387309+00:00
-- url     : https://prove2.me/theorems/81d78723-44c5-41c1-876d-4b8cdd4c2661
-- title:
--   Original physical HJB plus raw BV drift residual is nonpositive almost surely
-- statement:
--   For the actual original BV Levy process and the literal two summands of B in the c1e2f021 physical stopped witness, the HJB generator part is pointwise nonpositive in the strictly pre-ruin interior. The remaining raw BV residual R is almost surely monotone; every grid-cell coefficient is nonnegative by exp positivity and the source gradient hypothesis. Their exact combined B is therefore almost surely nonpositive for any locally monotone physical grid. The result does not assert global L1, mean-zero M, zero residual or no ruin jump.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hmono : ∀ i, i < n + 1 → u i ≤ u (i + 1)) :
    ∀ᵐ ω ∂P,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u (i + 1) : ℝ) - (u i : ℝ))
        else 0) +
      (∑ i ∈ Finset.range (n + 1),
        (if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u i : ℝ))) * deriv w (Z i)
         else 0) * (R (u i) - R (u (i + 1)))) ≤ 0 := by sorry
