-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_compact_negative_jump_kernel_envelope
-- name    : AvramDividend.Classical.avram_p3_2_original_compact_negative_jump_kernel_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:46:39.661254+00:00
-- url     : https://prove2.me/theorems/c4d6e93c-c3c5-4020-9b46-6645cd7f1b14
-- title:
--   Original BV compact negative-jump nonlinear kernel has uniform small/large mark envelope
-- statement:
--   On a compact strictly positive reserve strip a≤y≤b, the actual negative Lévy jump kernel w(y+z)−w(y) has bound L|z| for marks at least −a/2, and bound 2R for larger negative marks, under E2's exact local Lipschitz condition and global below-b bound. This produces the BV-integrable small-jump and finite-rate large-jump envelope used in the original-process stochastic compensation and mesh limit, with no assumption that large jumps remain in the interior.
-- source:
--   Elementary analytic split of the exact compact Lipschitz and below-b assumptions of the Proved original E2 signed L1 theorem 3497711e.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Source-exact compact BV nonlinear negative-mark kernel envelope:
small marks are first-order Lipschitz, large marks uniformly bounded. -/

theorem AvramDividend.Classical.avram_p3_2_original_compact_negative_jump_kernel_envelope
    (w : ℝ → ℝ) (a b L R : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (y z : ℝ) (hy : y ∈ Set.Icc a b) (hz : z < 0) :
    |w (y + z) - w y| ≤
      if -(a / 2) ≤ z then L * |z| else 2 * R := by sorry
