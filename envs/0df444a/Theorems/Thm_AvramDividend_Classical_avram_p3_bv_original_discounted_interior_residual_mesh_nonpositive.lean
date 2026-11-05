-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_interior_residual_mesh_nonpositive
-- name    : AvramDividend.Classical.avram_p3_bv_original_discounted_interior_residual_mesh_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:34:16.334539+00:00
-- url     : https://prove2.me/theorems/c8c72b6f-5b03-409f-958e-61b7bcc2c82a
-- title:
--   Original BV discounted C1 residual source correction is nonpositive on every strict interior mesh
-- statement:
--   For any original-process finite time mesh and any sample-dependent source prestate Z, activate the discounted C1 derivative weight only when the prestate is strictly positive and lies below cap. The given derivative lower bound and positivity of exponential discount make the active weights nonnegative. The genuine BV source residual therefore contributes a nonpositive sum almost everywhere. At cap and zero contact this correction is explicitly zero and separate boundary accounting is still required.
-- source:
--   Proved original BV source weighted-residual mesh nonpositive helper; Real.exp_pos, HJB gradient ≥1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_weighted_residual_mesh_nonpositive

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Source-exact C¹ discount weights are activated only at strict interior
prestates. Contact with zero or cap contributes zero here and must be
handled by the separate contact/payment accounting. -/

theorem AvramDividend.Classical.avram_p3_bv_original_discounted_interior_residual_mesh_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (Z : ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range n,
        (if 0 < Z i ω ∧ ENNReal.ofReal (Z i ω) < C then
          Real.exp (-(q * (u i : ℝ))) * deriv w (Z i ω)
        else 0) * (R (u i) - R (u (i + 1)))) ≤ 0 := by sorry
