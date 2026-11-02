-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_finite_cap_uniform_dividend_secant_residual_bound
-- name    : AvramDividend.Classical.avram_wave5_04b_finite_cap_uniform_dividend_secant_residual_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:56:32.435988+00:00
-- url     : https://prove2.me/theorems/bfdfdf06-a340-4296-baa8-ef2ebfd9f6a8
-- title:
--   Finite-cap uniform bound on global derivative-free dividend secant residual
-- statement:
--   For an explicit finite positive cap and the slope-one cap-linear extension V, the incremental correction V(y+δ)-V(y)-δ is nonnegative and uniformly bounded above by the monotone transformed endpoint gap (w(C)-C)-w(0), for every y≥0 and δ≥0. The bound is independent of controlled source path, dividend variation, and payment time, and it can support automatic integrability against the finite-horizon actual dividend measure once measurability is supplied. Does not evaluate derivatives at zero or cap.
-- source:
--   import Mathlib
--   import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal
--   open AvramDividend.Classical
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- A finite cap bounds the entire incremental dividend-control secant
--   residual uniformly on nonnegative reserves, with no boundary derivative. -/
--   theorem solution
--       (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤)
--       (w V : ℝ → ℝ)
--       (hw_cont : ContinuousOn w (Ici 0))
--       (hw_smooth : ContDiffOn ℝ 1 w
--         {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
--       (hw_grad : ∀ z : ℝ, 0 < z →
--         ENNReal.ofReal z < C → 1 ≤ deriv w z)
--       (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
--         V z = if z ≤ C.toReal then w z
--           else w C.toReal + (z - C.toReal))
--       (y δ : ℝ) (hy : 0 ≤ y) (hδ : 0 ≤ δ) :
--       0 ≤ V (y + δ) - V y - δ ∧
--         V (y + δ) - V y - δ ≤
--           (w C.toReal - C.toReal) - w 0 := by
--     have hVtop : C = ⊤ → ∀ z : ℝ, V z = w z := by
--       intro h
--       exact (hCfinite h).elim
--     have hC0 : (0 : ℝ) ≤ C.toReal := ENNReal.toReal_nonneg
--     have hV0 : V 0 = w 0 := by
--       simpa [hC0] using (hVfinite hCfinite 0)
--     have hVC : V C.toReal = w C.toReal := by
--       simpa using (hVfinite hCfinite C.toReal)
--     have hOrder : y ≤ y + δ := le_add_of_nonneg_right hδ
--     have hSecZero := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
--       C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
--       0 y (le_refl (0 : ℝ)) hy
--     have hSecStep := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
--       C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
--       y (y + δ) hy hOrder
--     have hLower : w 0 ≤ V y - y := by
--       linarith only [hSecZero, hV0]
--     have hUpper : V (y + δ) - (y + δ) ≤
--         w C.toReal - C.toReal := by
--       by_cases hBelow : y + δ ≤ C.toReal
--       · have hSecCap := avram_wave5_04b_positive_ennreal_cap_extension_global_secant
--           C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
--           (y + δ) C.toReal (by linarith only [hy, hδ]) hBelow
--         linarith only [hSecCap, hVC]
--       · have hAbove : ¬ y + δ ≤ C.toReal := hBelow
--         have hVAbove : V (y + δ) =
--             w C.toReal + ((y + δ) - C.toReal) := by
--           simpa [hAbove] using (hVfinite hCfinite (y + δ))
--         linarith only [hVAbove]
--     constructor
--     · linarith only [hSecStep]
--     · linarith only [hLower, hUpper]

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_finite_cap_uniform_dividend_secant_residual_bound
    (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (y δ : ℝ) (hy : 0 ≤ y) (hδ : 0 ≤ δ) :
    0 ≤ V (y + δ) - V y - δ ∧
      V (y + δ) - V y - δ ≤
        (w C.toReal - C.toReal) - w 0 := by sorry
