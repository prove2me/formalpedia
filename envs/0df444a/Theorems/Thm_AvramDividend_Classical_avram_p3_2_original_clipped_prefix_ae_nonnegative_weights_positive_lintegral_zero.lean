-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_prefix_ae_nonnegative_weights_positive_lintegral_zero
-- name    : AvramDividend.Classical.avram_p3_2_original_clipped_prefix_ae_nonnegative_weights_positive_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:57:50.504956+00:00
-- url     : https://prove2.me/theorems/1fdd2386-5e95-4b36-b5e1-344b1b01c8c3
-- title:
--   Original BV stopped finite-prefix nonlinear residual vanishes for almost-surely nonnegative random weights
-- statement:
--   For genuine bounded-variation Levy X and original admissible dividend process D, any random stopped finite-prefix physical partition and weights that are nonnegative almost surely in every cell produce zero positive outer integral of the intrinsic nonlinear residual, without requiring pointwise weight nonnegativity or signed R integrability.
-- source:
--   Uses Proved/public 22640b97-374a-4109-90ed-b0a55816fba1 for weights clipped to their nonnegative part, and almost-sure equality of clipped and original weighted physical sums.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_finite_prefix_arbitrary_weights_positive_lintegral_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_clipped_prefix_ae_nonnegative_weights_positive_lintegral_zero
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
    (ha : ∀ᵐ ω ∂P, ∀ i, 0 ≤ a ω i) :
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
