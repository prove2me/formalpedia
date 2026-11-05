-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_strict_cap_C1_Lipschitz
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_strict_cap_C1_Lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:37:23.478777+00:00
-- url     : https://prove2.me/theorems/eb7decd4-58c9-4c79-aac8-071b6cca3197
-- title:
--   Original strict HJB cap C1 regularity implies exact stopped-compensator Lipschitz bound
-- statement:
--   On the canonical original strict-HJB smoothness region {y>0, ofReal y<C}, if the stopped interior band [a/2,b] lies strictly below cap C, C1 smoothness gives the exact finite local Lipschitz constant used by original nonlinear negative-jump compensation, without an additional abstract derivative bound or arbitrary Lipschitz axiom.
-- source:
--   Public Proved P3-E original_C1_open_interior_Lipschitz b4ebfe59 and source_HJB_strict_cap_band_open 74aac065.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_C1_open_interior_Lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_source_HJB_strict_cap_band_open
open MeasureTheory Set Topology AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_strict_cap_C1_Lipschitz
(C : ℝ≥0∞) (w : ℝ → ℝ) (a b : ℝ)
(ha : 0 < a) (hab : a ≤ b) (hbC : ENNReal.ofReal b < C)
(hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
∃ L : ℝ, 0 ≤ L ∧
  ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v| := by sorry
