-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_finite_prefix_arbitrary_weights_positive_lintegral_zero
-- name    : AvramDividend.Classical.avram_p3_2_original_clipped_finite_prefix_arbitrary_weights_positive_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:50:55.972666+00:00
-- url     : https://prove2.me/theorems/22640b97-374a-4109-90ed-b0a55816fba1
-- title:
--   Original BV random clipped finite-prefix physical grid correction vanishes for all nonnegative random weights
-- statement:
--   For the original bounded-variation Levy X and original dividend process D, the nonlinear intrinsic residual sampled on an arbitrary random finite stopped partition has zero positive outer expectation for arbitrary nonnegative sample- and cell-dependent weights even when monotonicity holds only on used cells, with an unconstrained unused grid tail.
-- source:
--   Combines Proved/public original arbitrary nonnegative weighted clipped-grid positive-outer-zero 4ed02621-cc37-4448-a0b2-76ca23baf974 with finite used-prefix freezing; identifies every used cell exactly.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_arbitrary_nonnegative_weights_positive_lintegral_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_clipped_finite_prefix_arbitrary_weights_positive_lintegral_zero
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
    (τ : Ω → ℝ≥0) (u : Ω → ℕ → ℝ≥0)
    (n : Ω → ℕ) (a : Ω → ℕ → ℝ)
    (hu : ∀ ω i, i < n ω → u ω i ≤ u ω (i + 1))
    (ha : ∀ ω i, 0 ≤ a ω i) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let G : Ω → ℝ := fun ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u ω i) (τ ω)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      ∑ i : Fin (n ω),
        a ω i *
          (V (riskProcess X x D (v i) ω -
            (R (v (i + 1)) - R (v i))) -
           V (riskProcess X x D (v i) ω))
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) = 0 := by sorry
