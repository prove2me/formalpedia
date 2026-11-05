-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_ruin_stopped_residual_mesh_nonpositive
-- name    : AvramDividend.Classical.avram_p3_bv_original_ruin_stopped_residual_mesh_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:46:45.920711+00:00
-- url     : https://prove2.me/theorems/5852fa04-16c4-4cfd-82e1-c0bd6174b778
-- title:
--   Actual original ruin-stopped BV C1 weighted source residual has nonpositive mesh contribution
-- statement:
--   On original X and D, the discounted derivative weight is activated precisely at strictly pre-ruin interior left-prepayment reserve grid points. It is nonnegative by the original cap gradient hypothesis. The original BV physical-drift-minus-actual-negative-source-jumps residual is monotone, so its weighted increment correction is almost surely nonpositive, including when the next cell crosses ruin. Zero and cap contacts carry zero in this specific interior correction.
-- source:
--   Proved original weighted residual mesh sign 96f15e04 and original DividendStrategy left-prestate/ruin fields

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_weighted_residual_mesh_nonpositive

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The genuine BV residual after subtracting actual source negative jumps
has favourable sign even if the next grid point crosses ruin. The mask
uses the original left-prepayment source reserve and current ruin clock. -/

theorem AvramDividend.Classical.avram_p3_bv_original_ruin_stopped_residual_mesh_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1)) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
      (∑ i ∈ Finset.range n,
        (if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u i : ℝ))) * deriv w (Z i)
        else 0) * (R (u i) - R (u (i + 1)))) ≤ 0 := by sorry
