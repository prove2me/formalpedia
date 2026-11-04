-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_compact_derivative_implies_lipschitz
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_compact_derivative_implies_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:17:01.053064+00:00
-- url     : https://prove2.me/theorems/596e81d8-37d8-48bd-a514-2336628eaded
-- title:
--   Original BV compact derivative norm yields a reserve-band Lipschitz estimate
-- statement:
--   For the original bounded-variation candidate, a uniform nonnegative derivative norm bound at each point of a compact real reserve band implies the matching uniform Lipschitz estimate between any two reserves in that band. This is the local increment estimate needed to dominate small negative Lévy jumps.
-- source:
--   Pinned Mathlib Convex.lipschitzOnWith_of_nnnorm_deriv_le (revision 0df444a360eaa60ab8c11dca51a86af692955474), serving the original BV physical jump integrability interface.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_compact_derivative_implies_lipschitz (w : ℝ → ℝ) (a b : ℝ) (L : ℝ≥0)
  (hDiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ w x)
  (hDeriv : ∀ x ∈ Icc a b, ‖deriv w x‖₊ ≤ L) :
  ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
    |w u - w v| ≤ (L : ℝ) * |u - v| := by sorry
