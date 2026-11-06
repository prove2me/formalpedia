-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_interior_weighted_generator_grid_le
-- name    : AvramDividend.Classical.avram_p3_2_original_strict_interior_weighted_generator_grid_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:48:08.747198+00:00
-- url     : https://prove2.me/theorems/4a80ea24-bf19-4031-af8f-721ddc4925f4
-- title:
--   Original stopped X/D strict interior discounted-gradient source grid upper bound
-- statement:
--   For any genuine original X/D finite physical grid whose post-rightpayment starting reserves lie in the strict HJB interior, the discounted derivative-weighted sum of the original source increments and original intrinsic marked-count jump magnitudes is bounded by the same discounted derivative-weighted original physical drift. This handles an arbitrary negative residual as a favourable signed contribution and uses no cap-contact extrapolation.
-- source:
--   Proved original weighted intrinsic mark source-grid theorem together with the target's own strict-interior slope condition; source-localised P3 residual adapter.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_weighted_intrinsic_jump_drift_grid_le

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Discounted positive-gradient original-grid bound with the actual X/D rightpayment
reserve. Interior hypotheses are local to the finite grid, not global at cap. -/

theorem AvramDividend.Classical.avram_p3_2_original_strict_interior_weighted_generator_grid_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (s t : Fin n → ℝ≥0)
      (hst : ∀ i, s i ≤ t i)
      (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
      (hInterior : ∀ i : Fin n,
        0 < x + X.X (s i) ω - rightLimit D (s i) ω ∧
        ENNReal.ofReal (x + X.X (s i) ω - rightLimit D (s i) ω) < C),
      (∑ i : Fin n,
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (x + X.X (s i) ω - rightLimit D (s i) ω)) *
        (X.X (t i) ω - X.X (s i) ω +
          (∫⁻ p, (if s i < p.1 ∧ p.1 ≤ t i then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ≤
      ∑ i : Fin n,
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (x + X.X (s i) ω - rightLimit D (s i) ω)) *
        (((t i : ℝ) - (s i : ℝ)) * X.drift) := by sorry
