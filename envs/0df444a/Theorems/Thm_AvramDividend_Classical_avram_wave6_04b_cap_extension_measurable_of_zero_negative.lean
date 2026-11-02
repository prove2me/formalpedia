-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative
-- name    : AvramDividend.Classical.avram_wave6_04b_cap_extension_measurable_of_zero_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:46:34.778844+00:00
-- url     : https://prove2.me/theorems/0e054a59-428c-4931-9922-9483d22a6b08
-- title:
--   Cap-linear HJB extension is Borel measurable with zero-negative candidate
-- statement:
--   A candidate w continuous on the closed nonnegative reserve half-line and identically zero below zero is Borel measurable, even if its value jumps at zero. Its slope-one cap-linear extension V is therefore Borel measurable on all real capital for either a finite cap or an infinite cap. This closes the potential-measurability obligation in the original positive-cap dividend Stieltjes correction without postulating global smoothness or endpoint derivatives.
-- source:
--   import Mathlib
--
--   open MeasureTheory Set
--   open scoped NNReal ENNReal
--
--   set_option pp.explicit true
--   set_option pp.fullNames true
--   set_option pp.universes true
--
--   /-- The cap-linear extension of a nonnegative-side continuous HJB candidate,
--   zero on negative capital, is Borel measurable for every finite/infinite cap. -/
--   theorem AvramDividend.Classical.avram_wave6_04b_cap_extension_measurable_of_zero_negative
--       (w V : ℝ → ℝ) (C : ℝ≥0∞)
--       (hw_cont : ContinuousOn w (Ici 0))
--       (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
--       (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
--       (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
--         V y = if y ≤ C.toReal then w y
--           else w C.toReal + (y - C.toReal)) :
--       Measurable V := by
--     have hwPiece : Measurable
--         ((Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ))) :=
--       hw_cont.measurable_piecewise continuous_const.continuousOn
--         measurableSet_Ici
--     have hwEq : (Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ)) = w := by
--       funext y
--       by_cases hy : 0 ≤ y
--       · simp [Set.piecewise, Set.mem_Ici, hy]
--       · have hlt : y < 0 := lt_of_not_ge hy
--         simp [Set.piecewise, Set.mem_Ici, hy, hw_neg y hlt]
--     have hwMeas : Measurable w := by
--       rw [← hwEq]
--       exact hwPiece
--     by_cases htop : C = ⊤
--     · have hVeq : V = w := by
--         funext y
--         exact hVtop htop y
--       rw [hVeq]
--       exact hwMeas
--     · have hLin : Measurable (fun y : ℝ =>
--           w C.toReal + (y - C.toReal)) :=
--         measurable_const.add (measurable_id.sub measurable_const)
--       have hPiece : Measurable
--           ((Iic C.toReal).piecewise w
--             (fun y : ℝ => w C.toReal + (y - C.toReal))) :=
--         hwMeas.piecewise hLin measurableSet_Iic
--       have hVeq : V = (Iic C.toReal).piecewise w
--           (fun y : ℝ => w C.toReal + (y - C.toReal)) := by
--         funext y
--         rw [hVfinite htop y]
--         simp [Set.piecewise, Set.mem_Iic]
--       rw [hVeq]
--       exact hPiece

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave6_04b_cap_extension_measurable_of_zero_negative
    (w V : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal)) :
    Measurable V := by sorry
