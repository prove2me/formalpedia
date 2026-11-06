-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_uniform_all_nonnegative_grid_weights_nonlinear_R_nonpos
-- name    : AvramDividend.Classical.avram_p3_2_original_uniform_all_nonnegative_grid_weights_nonlinear_R_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:43:19.3022+00:00
-- url     : https://prove2.me/theorems/17403abb-4528-4578-a664-e152ecce9427
-- title:
--   One original BV full-probability event controls every physical grid and nonnegative cell weight
-- statement:
--   For original bounded-variation spectrally negative Levy X and true dividend strategy D, there is one full-probability event on which every monotone physical time grid, every finite number of cells, and every nonnegative real choice of weights, including choices depending on the original path, have a nonpositive cap-linear nonlinear intrinsic-jump correction. The common exceptional null event is independent of the grid and the weights, and does not require signed correction L1.
-- source:
--   Proved/public original-X R monotonicity 3c2f33da-f3ab-4a64-9515-4b9915de69b2 on a single a.e event and Proved positive-cap C1 extension monotonicity 5e9573dd-9dc4-423e-a46f-8048ae9f477d. Apply monotonicity cellwise and sum arbitrary nonnegative weights, preserving a uniform null event.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_uniform_all_nonnegative_grid_weights_nonlinear_R_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P,
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u)
        (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i),
        (∑ i : Fin n,
          a i *
            (V (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))) -
             V (riskProcess X x D (u i) ω))) ≤ 0 := by sorry
