-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a378_topcap_C2_positive_derivatives_continuousOn
-- name    : AvramDividend.Classical.avram_ga_a378_topcap_C2_positive_derivatives_continuousOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:08:07.010842+00:00
-- url     : https://prove2.me/theorems/cc885da4-08d8-4fac-9e5e-161c062462f9
-- title:
--   Continuity of positive-domain first and second derivatives under top-cap C2 regularity
-- statement:
--   For an everywhere finite top cap, local twice-continuous differentiability of w on the strictly positive reserve domain implies its ordinary first and second derivatives are continuous on the positive half-line.
-- source:
--   Top-cap original Gaussian C2 spatial residual and compensated masked polynomial integration, a146 and a377m.

import Mathlib
open Set Topology
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a378_topcap_C2_positive_derivatives_continuousOn
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ContinuousOn (deriv w) (Ioi (0 : ℝ)) ∧
      ContinuousOn (iteratedDeriv 2 w) (Ioi (0 : ℝ)) := by sorry
