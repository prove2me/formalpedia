-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_uniform_all_stopped_finite_prefix_weighted_R_nonpos
-- name    : AvramDividend.Classical.avram_p3_2_original_uniform_all_stopped_finite_prefix_weighted_R_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:53:31.201257+00:00
-- url     : https://prove2.me/theorems/4e449c9b-1e6a-496b-a8b5-0d9ba2f92294
-- title:
--   One original BV full-probability event controls all random clipped finite-prefix weighted residuals
-- statement:
--   For genuine bounded-variation Levy X and original dividend process D, there is one full-probability set of paths on which every arbitrary finite prefix with ordered used cells, any stopping clock, and arbitrary nonnegative cell weights has a nonpositive nonlinear residual correction. Unused future grid cells are unrestricted.
-- source:
--   Proved/public 17403abb-4528-4578-a664-e152ecce9427 original uniform all-grid weighted sign, plus finite-prefix tail freezing and monotone truncation. No new stochastic hypotheses.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_uniform_all_nonnegative_grid_weights_nonlinear_R_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_uniform_all_stopped_finite_prefix_weighted_R_nonpos
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
      ∀ (τ : ℝ≥0) (u : ℕ → ℝ≥0) (n : ℕ)
        (hu : ∀ i, i < n → u i ≤ u (i + 1))
        (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i),
        let v : ℕ → ℝ≥0 := fun j => min (u (min j n)) τ
        (∑ i : Fin n,
          a i *
            (V (riskProcess X x D (v i) ω -
              (R (v (i + 1)) - R (v i))) -
             V (riskProcess X x D (v i) ω))) ≤ 0 := by sorry
