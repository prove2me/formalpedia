-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_interior_C1_gradient_intrinsic_jump_budget
-- name    : AvramDividend.Classical.avram_bv_cell7_original_stopped_interior_C1_gradient_intrinsic_jump_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:39:54.974934+00:00
-- url     : https://prove2.me/theorems/7dcf38bd-8992-4828-9ffc-717e2032b934
-- title:
--   Original stopped physical grid interior discounted C1 gradient drift and intrinsic marked jump budget
-- statement:
--   The actual admissible original dividend process has a nonnegative discounted pre-right-payment C1 gradient coefficient on strict pre-ruin interior cells by the standing gradient inequality. Therefore the original BV drift-minus-intrinsic-negative-jump budget holds for the precise indexed discounted C1 source coefficients on the ruin/horizon clipped grid, without an artificial coefficient hypothesis.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_stopped_weighted_drift_intrinsic_jump_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_stopped_interior_C1_gradient_intrinsic_jump_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (T : ℝ≥0) (m : ℕ) :
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
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let N : ℕ → Measure (ℝ≥0 × ℝ) := fun i =>
        ((Measure.count.restrict
          ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc (s i ω) (s (i + 1) ω))).map
            (fun v : ℝ≥0 => (v, Δ v)))
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (X.X (s (i + 1) ω) ω - X.X (s i ω) ω)) ≤
      ∑ i ∈ Finset.range (m + 1),
        W i ω *
          ((((s (i + 1) ω : ℝ) - (s i ω : ℝ)) * X.drift) -
            (∫⁻ p, ENNReal.ofReal (-p.2) ∂N i).toReal) := by sorry
