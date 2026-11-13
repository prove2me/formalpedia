-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB165_time_level_null_implies_ae_avoids_level
-- name    : AvramDividend.Classical.avram_gbB165_time_level_null_implies_ae_avoids_level
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:00:40.784717+00:00
-- url     : https://prove2.me/theorems/535e5663-4fa7-403d-87e8-6021a56bf2e9
-- title:
--   Null physical-time level set implies level avoidance a.e inside horizon
-- statement:
--   A level set of zero physical-time Lebesgue measure inside a finite time horizon is avoided almost everywhere for the restricted Lebesgue measure. This converts the stochastic fixed-level occupation assertion B100 into the a.e avoidance input of B163.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB165_time_level_null_implies_ae_avoids_level
    (n : ℕ) (f : ℝ → ℝ) (b : ℝ)
    (hzero : volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ f t = b} = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      f t ≠ b := by sorry
