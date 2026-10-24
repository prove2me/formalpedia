-- Prove2me | Theorems.Thm_AvramDividend_Classical_tilted_monotone_implies_exit_decay
-- name    : AvramDividend.Classical.tilted_monotone_implies_exit_decay
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:53:58.648224+00:00
-- url     : https://prove2.me/theorems/b5d3e4fd-f321-4a3d-8e9b-31ea7ba9fe28
-- title:
--   Esscher-tilted monotonicity implies the exponential scale comparison
-- statement:
--   For any real W and φ, monotonicity of x ↦ exp(-φx)W(x) on the positive half-line implies W(x) ≤ exp(-φ(y-x))W(y) whenever 0<x≤y. This is the converse of the already Proved exit_decay_implies_tilted_monotone and permits a future independent proof of tilted monotonicity to close the two unbounded Esscher scale-decay milestones.
-- source:
--   Elementary positive-exponential multiplication; converse to published AvramDividend.Classical.exit_decay_implies_tilted_monotone, in the Avram Dividend Classical scale-function branch.

import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Mathlib.Tactic.Ring
open AvramDividend.Classical Set

theorem AvramDividend.Classical.tilted_monotone_implies_exit_decay (W : ℝ → ℝ) (φ : ℝ)
    (htilt : MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y := by sorry
