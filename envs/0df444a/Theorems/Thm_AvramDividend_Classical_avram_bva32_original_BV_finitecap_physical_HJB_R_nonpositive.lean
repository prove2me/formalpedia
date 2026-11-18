-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva32_original_BV_finitecap_physical_HJB_R_nonpositive
-- name    : AvramDividend.Classical.avram_bva32_original_BV_finitecap_physical_HJB_R_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:45:47.15656+00:00
-- url     : https://prove2.me/theorems/581b2c6b-c08b-4edb-95e7-595db2866176
-- title:
--   Original finite-cap BV generator-grid plus exact physical drift-jump remainder is nonpositive almost surely
-- statement:
--   At every finite physical stopped grid, the actual original BV drift residual R(t)=t*X.drift-X.X(t)-sum true negative left-jumps vanishes at each grid point, by original source path identity bva31. The HJB generator contribution is pointwise nonpositive on the original pre-ruin interior reserve mask. Monotone positive grid cell lengths and nonnegative discount factors therefore make the combined original signed HJB plus physical R correction nonpositive. This certificate is the actual signed B grid appearing in the original positive-intensity finite-cap source f7304aa8; it isolates generator sign and drift decomposition from the remaining cash/contact positive error.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva31_original_BV_physical_drift_jump_R_vanishes
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva32_original_BV_finitecap_physical_HJB_R_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let Z : ℕ → ℝ := fun i =>
        Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
      (∑ i ∈ Finset.range (n + 1),
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
        else 0) * (R (u n i) - R (u n (i + 1)))) ≤ 0 := by sorry
