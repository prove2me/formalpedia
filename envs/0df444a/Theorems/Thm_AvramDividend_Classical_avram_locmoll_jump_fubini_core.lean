-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_jump_fubini_core
-- name    : AvramDividend.Classical.avram_locmoll_jump_fubini_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:41:47.861195+00:00
-- url     : https://prove2.me/theorems/5618c0da-5bb5-519d-baac-1e88dff35da1
-- title:
--   Product-integrable negative jump kernel with pointwise convolution gives the full integral interchange
-- statement:
--   Product-integrable negative jump kernel with pointwise convolution gives the full integral interchange
-- source:
--   Avram Proposition 4(i), child of 10e0ec45-30d2-5555-bcde-5adae9d0be9f

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Convolution
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_jump_fubini_core
    (ν : Measure ℝ) [SFinite ν] (ρ : ℝ → ℝ)
    (K : ℝ → ℝ → ℝ) (G : ℝ → ℝ)
    (hP : Integrable (fun p : ℝ × ℝ => ρ p.1 * K p.1 p.2) (volume.prod ν))
    (he : ∀ᵐ z ∂ν, G z = ∫ r, ρ r * K r z) :
    Integrable G ν ∧ Integrable (fun r => ρ r * (∫ z, K r z ∂ν)) ∧
      (∫ z, G z ∂ν) = ∫ r, ρ r * (∫ z, K r z ∂ν) := by sorry
