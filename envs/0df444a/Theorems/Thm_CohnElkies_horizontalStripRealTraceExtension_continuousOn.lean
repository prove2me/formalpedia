-- Prove2me | Theorems.Thm_CohnElkies_horizontalStripRealTraceExtension_continuousOn
-- name    : CohnElkies.horizontalStripRealTraceExtension_continuousOn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/e4130313-ba1d-479f-b5a7-16f5e90cc40d
-- title:
--   CohnElkies.horizontalStripRealTraceExtension_continuousOn
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology

theorem CohnElkies.horizontalStripRealTraceExtension_continuousOn
    {a b : ℝ} (hab : a < b)
    (H : ℂ → ℝ) (bottom top : ℝ → ℝ)
    (hH : ContinuousOn H (Complex.im ⁻¹' Ioo a b))
    (hbottom : Continuous bottom)
    (htop : Continuous top)
    (hbottomtrace : ∀ s : ℝ,
      Tendsto H
        (𝓝[Complex.im ⁻¹' Ioo a b]
          ((s : ℂ) + Complex.I * (a : ℂ)))
        (𝓝 (bottom s)))
    (htoptrace : ∀ s : ℝ,
      Tendsto H
        (𝓝[Complex.im ⁻¹' Ioo a b]
          ((s : ℂ) + Complex.I * (b : ℂ)))
        (𝓝 (top s))) :
    ContinuousOn
      (horizontalStripRealTraceExtension a b H bottom top)
      (Complex.im ⁻¹' Icc a b) := by sorry
