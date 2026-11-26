-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_compact_convolution_jet
-- name    : AvramDividend.Classical.avram_locmoll_compact_convolution_jet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:41:47.175288+00:00
-- url     : https://prove2.me/theorems/04bbfb49-318a-556f-8808-0b0b0de71ce4
-- title:
--   Derivative and second derivative of convolution with a compact C2 function
-- statement:
--   Derivative and second derivative of convolution with a compact C2 function
-- source:
--   Avram Proposition 4(i), child of 06cb2549-7f74-48bc-a6ba-0890037b26d6

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Convolution
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_compact_convolution_jet
    (ρ F : ℝ → ℝ) (hρ : Integrable ρ)
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (y : ℝ) :
    Integrable (fun r => ρ r * F (y - r)) ∧
    Integrable (fun r => ρ r * deriv F (y - r)) ∧
    Integrable (fun r => ρ r * iteratedDeriv 2 F (y - r)) ∧
    deriv (fun t => ∫ r, ρ r * F (t - r)) y =
      (∫ r, ρ r * deriv F (y - r)) ∧
    iteratedDeriv 2 (fun t => ∫ r, ρ r * F (t - r)) y =
      (∫ r, ρ r * iteratedDeriv 2 F (y - r)) := by sorry
