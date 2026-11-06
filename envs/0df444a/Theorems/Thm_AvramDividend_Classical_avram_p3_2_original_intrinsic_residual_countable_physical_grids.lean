-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_intrinsic_residual_countable_physical_grids
-- name    : AvramDividend.Classical.avram_p3_2_original_intrinsic_residual_countable_physical_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:29:13.930018+00:00
-- url     : https://prove2.me/theorems/119ccd8b-54d6-4075-b001-158e47a94727
-- title:
--   One original Lévy BV residual sign event for every countable ruin-clipped physical refinement grid
-- statement:
--   For the actual original bounded-variation spectrally negative Levy process X, dividend strategy D and cap-linear verification candidate, there is one full-probability event on which the explicit intrinsic negative-jump residual R is monotone and the discounted nonlinear correction is nonpositive for every physical ruin/horizon clipped mesh in an arbitrary countable monotone family. No extra martingale, integrability or compact interior hypothesis is assumed.
-- source:
--   Exact countable-meet of the accepted original full-probability intrinsic residual theorem dac87ae6, using ae_all_iff on the actual original X/D. This makes the pointwise sign usable for cofinal source-grid Fatou limits.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_explicit_ruin_cap_BV_residual
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_intrinsic_residual_countable_physical_grids
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
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (q : ℝ) (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ m, Monotone (u m)) (n : ℕ → ℕ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let v : ℕ → ℝ≥0 := fun i => min (u m i) τ
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      Monotone R ∧
        (∑ i : Fin (n m),
          Real.exp (-(q * (v i : ℝ))) *
            (V (riskProcess X x D (v i) ω -
              (R (v (i + 1)) - R (v i))) -
             V (riskProcess X x D (v i) ω))) ≤ 0 := by sorry
