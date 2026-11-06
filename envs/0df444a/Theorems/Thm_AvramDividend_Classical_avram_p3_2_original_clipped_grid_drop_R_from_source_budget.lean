-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_grid_drop_R_from_source_budget
-- name    : AvramDividend.Classical.avram_p3_2_original_clipped_grid_drop_R_from_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:25:01.043421+00:00
-- url     : https://prove2.me/theorems/19b88da1-8d85-4044-9dbd-f8175dc499c5
-- title:
--   Original stopped BV clipped-grid signed cash source budget discards intrinsic R without L1
-- statement:
--   For the literal original bounded-variation Lévy reserve and cap-linear value function, consider any path-dependent monotone physical grid clipped at any path-dependent stop and with an arbitrary sample-dependent cell count. A genuine almost-sure pathwise cash/source inequality whose right-hand side includes the explicit intrinsic residual R correction implies the same inequality after discarding that correction. The lemma needs no L1 integrability or predictability of the correction and does not assert that the underlying raw pathwise cash-source inequality has already been constructed.
-- source:
--   Apply Proved/public universal original-X stopping-grid residual sign 3c2f33da-f3ab-4a64-9515-4b9915de69b2 to the clipped monotone grid on one full-measure event, then eliminate its nonpositive R correction from the stated genuine raw source-budget hypothesis.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_clipped_grid_drop_R_from_source_budget
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
    (hu : ∀ ω, Monotone (u ω))
    (n : Ω → ℕ) (F M B : Ω → ℝ)
    (hRaw :
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
      ∀ᵐ ω ∂P, F ω ≤ w x + (M ω + B ω) + G ω) :
    ∀ᵐ ω ∂P, F ω ≤ w x + (M ω + B ω) := by sorry
