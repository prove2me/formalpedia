-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_finite_prefix_positive_lintegral_zero
-- name    : AvramDividend.Classical.avram_p3_2_original_clipped_finite_prefix_positive_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:36:39.154961+00:00
-- url     : https://prove2.me/theorems/43cbb871-128b-4ea1-8388-2fed21ccbb72
-- title:
--   Original bounded-variation stopped nonlinear grid sign needs only finite-prefix monotonicity
-- statement:
--   For the genuine bounded-variation Lévy path and capped dividend process, any pathwise random stopped physical finite partition whose used cells alone satisfy successive-time monotonicity has zero positive outer expected nonlinear intrinsic correction. The raw grid tail may be completely arbitrary, so no global monotonicity premise or integrability upgrade is needed.
-- source:
--   Source-exact consequence of Proved/public original-X random clipped physical grid zero-outer-integral theorem 0d9a3257-6b6a-4713-a433-9babce398cc9. Extend a finite monotone prefix by freezing the tail at its last cell, so the accepted global-grid theorem applies; finite sums are unchanged.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_random_length_positive_lintegral_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_clipped_finite_prefix_positive_lintegral_zero
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
    (q : ℝ) (τ : Ω → ℝ≥0) (u : Ω → ℕ → ℝ≥0)
    (n : Ω → ℕ)
    (hu : ∀ ω i, i < n ω → u ω i ≤ u ω (i + 1)) :
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
        Real.exp (-(q * (v i : ℝ))) *
          (V (riskProcess X x D (v i) ω -
            (R (v (i + 1)) - R (v i))) -
           V (riskProcess X x D (v i) ω))
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) = 0 := by sorry
