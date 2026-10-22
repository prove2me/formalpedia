-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_lipschitz_time
-- name    : AvramDividend.Classical.gaussian_double_tail_atom_lipschitz_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:22:09.366861+00:00
-- url     : https://prove2.me/theorems/a45d2bcc-bc75-4847-94eb-9ec017fc7c98
-- title:
--   Esscher double-tail atom is Lipschitz in its time argument
-- statement:
--   At each fixed jump size z and Esscher rate φ, the positive-part double-tail atom t↦max(z−t,0)exp(−φz) has Lipschitz constant exp(−φz). This is useful for dominated-convergence or local Lipschitz regularity of Lévy double-tail kernels.
-- source:
--   Pinned Mathlib abs_max_sub_max_le_abs and Real.exp_pos.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_double_tail_atom_lipschitz_time
    (φ z s t : ℝ) :
    |max (z - t) 0 * Real.exp (-φ * z) -
      max (z - s) 0 * Real.exp (-φ * z)| ≤
      |t - s| * Real.exp (-φ * z) := by sorry
