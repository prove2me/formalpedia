-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_restricted_secant_convolution
-- name    : AvramDividend.Classical.avram_locmoll_restricted_secant_convolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:58:04.966429+00:00
-- url     : https://prove2.me/theorems/a67e10ab-9756-5732-908c-0bcd4926a416
-- title:
--   One-sided convolution preserves the slope on the translated interior
-- statement:
--   Restricted secant inequality for the actual translated arguments inside a finite cap, avoiding the stronger globally unit-slope extension assumption of 046dc2ca.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), localised one-sided smoothing route for cc518136-9d63-4167-8587-606274d8eec9

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_restricted_secant_convolution
    (μ : Measure ℝ) (ρ w : ℝ → ℝ)
    (ε a b c : ℝ) (hε : 0 < ε)
    (ha : 2 * ε ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hρI : Integrable ρ μ)
    (hρnorm : (∫ r, ρ r ∂μ) = 1)
    (hρpos : 0 ≤ᵐ[μ] ρ)
    (hρsupport : ∀ᵐ r ∂μ, ρ r ≠ 0 → r ∈ Icc ε (2 * ε))
    (hsec : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ c →
      v - u ≤ w v - w u)
    (haI : Integrable (fun r => ρ r * w (a - r)) μ)
    (hbI : Integrable (fun r => ρ r * w (b - r)) μ) :
    b - a ≤ (∫ r, ρ r * w (b - r) ∂μ) -
      (∫ r, ρ r * w (a - r) ∂μ) := by sorry
