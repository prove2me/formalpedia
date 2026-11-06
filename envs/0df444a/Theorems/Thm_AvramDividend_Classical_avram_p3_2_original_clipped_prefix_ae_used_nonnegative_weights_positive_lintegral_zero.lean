-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_prefix_ae_used_nonnegative_weights_positive_lintegral_zero
-- name    : AvramDividend.Classical.avram_p3_2_original_clipped_prefix_ae_used_nonnegative_weights_positive_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:00:03.717097+00:00
-- url     : https://prove2.me/theorems/94934afe-dd5e-4636-8e2a-3297068fa410
-- title:
--   Original BV random stopped nonlinear residual vanishes with only almost-sure positivity of used cell weights
-- statement:
--   The original BV intrinsic correction on a path-dependent ruin-clipped finite physical grid has zero positive outer integral if the weights are nonnegative almost surely on the used cells, even if all unused future weights are arbitrarily signed.
-- source:
--   Source-exact reduction to Proved/public original BV finite-prefix weighted zero-outer-integral theorem 22640b97 by clipping all weights at zero; finite sums sample only i<n ω so weight equality is needed only there.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_finite_prefix_arbitrary_weights_positive_lintegral_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_clipped_prefix_ae_used_nonnegative_weights_positive_lintegral_zero
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
