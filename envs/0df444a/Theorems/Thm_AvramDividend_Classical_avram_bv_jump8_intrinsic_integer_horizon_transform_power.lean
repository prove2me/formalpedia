-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_intrinsic_integer_horizon_transform_power
-- name    : AvramDividend.Classical.avram_bv_jump8_intrinsic_integer_horizon_transform_power
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T13:11:39.417795+00:00
-- url     : https://prove2.me/theorems/7c658e04-bd68-4ced-bc8a-670f8077473b
-- title:
--   Original intrinsic marked-jump Laplace transform has integer-horizon semigroup law
-- statement:
--   For each reciprocal mark cutoff, the weighted original intrinsic marked-jump exponential transform over (0,n] is the nth power of its transform over (0,1], including n=0. This requires measurability, disjoint physical-window independence for the original jump marks and stationary increments, not an unproved Poisson random measure assumption.
-- source:
--   Independent integer-time semigroup obligation for canonical 81b0ea8d. Prove that the intrinsic jump-mark functional is a measurable functional of the segment increment path, use the exact original independent and stationary increments plus cadlag regularity to obtain independent equal-law unit-window factors, then integrate their product.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_intrinsic_integer_horizon_transform_power
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then
        ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) = (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then
        ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) ^ n := by sorry
