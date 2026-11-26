-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_normalised_kernel
-- name    : AvramDividend.Classical.avram_locmoll_normalised_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T19:58:45.61082+00:00
-- url     : https://prove2.me/theorems/51f8c4b6-c677-5412-8976-cce66c07b8f4
-- title:
--   Normalised smooth nonnegative kernel supported inside the lower strip
-- statement:
--   Use Mathlib normalised ContDiffBump centred at δ/2 with radius δ/6.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), child of 2e269e44-0ec4-4d09-bac9-26533bf1d8ab

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_normalised_kernel
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ → ℝ,
      Integrable ρ ∧ (∫ r, ρ r) = 1 ∧
      (0 ≤ᵐ[volume] ρ) ∧
      (∀ᵐ r ∂volume, ρ r ≠ 0 →
        r ∈ Icc (δ / 3) (2 * (δ / 3))) ∧
      ContDiff ℝ 2 ρ ∧ HasCompactSupport ρ := by sorry
