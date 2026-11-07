-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_stopped_grid_HJB_residual_nonpositive
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_grid_HJB_residual_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:54:57.979005+00:00
-- url     : https://prove2.me/theorems/166eef1c-8939-4fc9-8234-8a97d1a2d94b
-- title:
--   Original stopped physical-grid C1 HJB generator and BV residual source has nonpositive sign
-- statement:
--   The actual bounded-variation Lévy and admissible dividend strategy, with the original HJB generator bound and interior derivative inequality, satisfy a pathwise nonpositive sum of exact original discounted generator cells and original BV residual increment cells on the stopped physical grid. This follows from original intrinsic jump-source reconciliation, the original drift bound and genuine HJB sign, without a stochastic surrogate or assumed source identity.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_interior_C1_gradient_intrinsic_jump_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_residual_intrinsic_marked_cell_identity
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_grid_HJB_residual_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (T : ℝ≥0) (m : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let s : ℕ → Ω → ℝ≥0 := fun i ω =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
    let Y : ℕ → Ω → ℝ := fun i ω => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (s i ω)
    let W : ℕ → Ω → ℝ := fun i ω =>
      if (s i ω : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Y i ω ∧ ENNReal.ofReal (Y i ω) < C then
        Real.exp (-(q * (s i ω : ℝ))) * deriv w (Y i ω)
      else 0
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (m + 1),
        (if (s i ω : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Y i ω ∧ ENNReal.ofReal (Y i ω) < C then
          Real.exp (-(q * (s i ω : ℝ))) *
            (X.generator w (Y i ω) - q * w (Y i ω)) *
            ((s (i + 1) ω : ℝ) - (s i ω : ℝ))
        else 0)) +
        (∑ i ∈ Finset.range (m + 1),
          W i ω * (R (s i ω) - R (s (i + 1) ω))) ≤ 0 := by sorry
