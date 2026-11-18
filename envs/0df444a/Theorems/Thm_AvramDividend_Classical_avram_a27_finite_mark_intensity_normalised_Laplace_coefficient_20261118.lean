-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_finite_mark_intensity_normalised_Laplace_coefficient_20261118
-- name    : AvramDividend.Classical.avram_a27_finite_mark_intensity_normalised_Laplace_coefficient_20261118
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:45:30.64152+00:00
-- url     : https://prove2.me/theorems/e58a8846-3921-426e-a9b5-a1a053097b33
-- title:
--   Finite positive mark intensity has normalised exponential factor in [0,1] and exact compensated rate identity
-- statement:
--   For any finite positive measure intensity on a mark set B, provided the exponential mark factor is integrable and lies in [0,1] almost everywhere, the intensity-normalised single-mark Laplace factor m lies in [0,1] and exactly satisfies r(m−1)=T∫B(exp(theta y)−1)dν when r=Tν(B). It extracts the purely analytic compensation from the source-space Mecke recurrence, independently of any stochastic jump marking representation.
-- source:
--   Pinned Mathlib integral_mono_ae, integral_sub, Real.exp_pos and finite nonnegative intensity arithmetic; auxiliary for A27 physical marked Mecke.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a27_finite_mark_intensity_normalised_Laplace_coefficient_20261118
    (ν : Measure ℝ) (B : Set ℝ) (θ : ℝ)
    (hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) B ν)
    (hExp : IntegrableOn (fun y : ℝ => Real.exp (θ * y)) B ν)
    (hBound : ∀ᵐ y ∂ν.restrict B,
      0 ≤ Real.exp (θ * y) ∧ Real.exp (θ * y) ≤ 1)
    (hMass : 0 < (ν B).toReal)
    (T r : ℝ) (hr : r = T * (ν B).toReal) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      r * (m - 1) = T *
        (∫ y in B, Real.exp (θ * y) - 1 ∂ν) := by sorry
