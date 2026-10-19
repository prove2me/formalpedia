-- Prove2me | Theorems.Thm_CohnElkies_lowerGammaScaledPositivePart_poisson_exponential_tail
-- name    : CohnElkies.lowerGammaScaledPositivePart_poisson_exponential_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/3344dc95-215d-46c1-8f75-a822ec5fa64d
-- title:
--   CohnElkies.lowerGammaScaledPositivePart_poisson_exponential_tail
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
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology

theorem CohnElkies.lowerGammaScaledPositivePart_poisson_exponential_tail
    {d : ℕ} (hd : 2 ≤ d) {c σ C S : ℝ}
    (hc : 0 < c) (hσ : 0 ≤ σ) (hσone : σ < 1)
    (hC : 0 < C)
    (hsupport :
      Function.support (lowerGammaScaledPositivePart d c) ⊆
        Icc (-C) C)
    (hmass :
      (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
        C * ((d : ℝ) / 2))
    (hS : C ≤ S) :
    (∫ Y : ℝ,
      stripPoissonKernel σ (S - Y) *
        lowerGammaScaledPositivePart d c Y) ≤
      (stripBottomMass σ * (Real.pi / 2) *
        Real.exp (-(Real.pi / 2) * (S - C))) *
          (C * ((d : ℝ) / 2)) := by sorry
