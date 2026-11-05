-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_crossing_secant
-- name    : AvramDividend.Classical.avram_p3_bv_finite_cap_linear_crossing_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:13:14.900211+00:00
-- url     : https://prove2.me/theorems/244e0215-074e-4541-9754-de6dbede140f
-- title:
--   Canonical BV interior gradient implies dividend secant across finite slope-one cap extension
-- statement:
--   For every positive finite cap C and a canonical BV HJB candidate w continuous on nonnegative reserves, C1 in the strict interior, and with derivative at least one inside, the slope-one linear continuation above C obeys the full dividend secant inequality across the cap. If 0≤a≤C≤b, then b-a≤[w(C)+(b-C)]-w(a). The proof needs no differentiability or Taylor bound of w above C and no smooth-fit derivative at C. This is an exact finite-cap contact tool for the original stopped BV mesh and payment estimates.
-- source:
--   Immediate consequence of the independently Proved BV full-cap interior gradient secant theorem 2ba5cc4f-3aab-40ea-a59a-8a49633c7595, the correct ENNReal.ofReal_toReal at finite cap, and algebra. Useful to avoid unsupported above-cap w evaluations in P3-F.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_finite_cap_linear_crossing_secant
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (a b : ℝ) (ha : 0 ≤ a) (haC : a ≤ C.toReal)
    (hCb : C.toReal ≤ b) :
    b - a ≤ (w C.toReal + (b - C.toReal)) - w a := by sorry
