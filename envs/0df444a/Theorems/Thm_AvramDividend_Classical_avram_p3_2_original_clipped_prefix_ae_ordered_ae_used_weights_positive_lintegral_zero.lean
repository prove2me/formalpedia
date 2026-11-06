-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_prefix_ae_ordered_ae_used_weights_positive_lintegral_zero
-- name    : AvramDividend.Classical.avram_p3_2_original_clipped_prefix_ae_ordered_ae_used_weights_positive_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:07:00.963134+00:00
-- url     : https://prove2.me/theorems/738ff151-c11f-4535-a2a5-e7979791c286
-- title:
--   Original stopped BV nonlinear residual vanishes for a.e. ordered random physical grids and a.e. nonnegative used weights
-- statement:
--   For genuine bounded-variation Levy X and its true original dividend process D, any randomly stopped finite physical grid has zero positive outer expected nonlinear intrinsic correction when grid order and used-weight nonnegativity both hold only almost surely. Bad null paths may carry entirely arbitrary grid and weights.
-- source:
--   Source-exact consequence of Proved/public 94934afe-dd5e-4636-8e2a-3297068fa410, replacing the physical grid on exceptional null paths by zero and using ae-congruence of positive outer integrals.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_prefix_ae_used_nonnegative_weights_positive_lintegral_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_clipped_prefix_ae_ordered_ae_used_weights_positive_lintegral_zero
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
    (hu : ∀ᵐ ω ∂P, ∀ i, i < n ω → u ω i ≤ u ω (i + 1))
    (ha : ∀ᵐ ω ∂P, ∀ i, i < n ω → 0 ≤ a ω i) :
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
