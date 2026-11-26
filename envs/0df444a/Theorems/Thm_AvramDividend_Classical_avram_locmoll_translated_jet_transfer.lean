-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_translated_jet_transfer
-- name    : AvramDividend.Classical.avram_locmoll_translated_jet_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:41:47.766427+00:00
-- url     : https://prove2.me/theorems/16a86a76-9c4a-5556-90fa-9e90d78f9135
-- title:
--   Local agreement of compact replacement transfers convolved jets and integrability
-- statement:
--   Local agreement of compact replacement transfers convolved jets and integrability
-- source:
--   Avram Proposition 4(i), child of 06cb2549-7f74-48bc-a6ba-0890037b26d6

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Convolution
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_translated_jet_transfer
    (w V F ρ : ℝ → ℝ) (δ y : ℝ) (hδ : 0 < δ)
    (hρ : Integrable ρ)
    (hs : ∀ᵐ r ∂volume, ρ r ≠ 0 → r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (he : ∀ z ∈ Ioo (y - 5 * δ / 6) (y - δ / 6), F z = w z ∧ V z = w z) :
    Integrable (fun r => ρ r * w (y - r)) ∧
    Integrable (fun r => ρ r * deriv w (y - r)) ∧
    Integrable (fun r => ρ r * iteratedDeriv 2 w (y - r)) ∧
    (∫ r, ρ r * V (y - r)) = (∫ r, ρ r * w (y - r)) ∧
    deriv (fun t => ∫ r, ρ r * V (t - r)) y =
      (∫ r, ρ r * deriv w (y - r)) ∧
    iteratedDeriv 2 (fun t => ∫ r, ρ r * V (t - r)) y =
      (∫ r, ρ r * iteratedDeriv 2 w (y - r)) := by sorry
