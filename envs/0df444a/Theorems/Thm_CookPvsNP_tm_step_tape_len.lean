-- Prove2me | Theorems.Thm_CookPvsNP_tm_step_tape_len
-- name    : CookPvsNP.tm_step_tape_len
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T07:04:26.471142+00:00
-- url     : https://prove2.me/theorems/efd5b425-95e0-4cdc-b660-f6ea7d5a0e8e
-- title:
--   One step of a one-tape machine grows the total tape by at most one square
-- statement:
--   In the one-tape model of Cook's Appendix the tape is a configuration `x q y`: a list `x` of symbols left of the head stored in reverse order, the scanned square, and a list `y` right of the head, with the tape extended implicitly by blanks to the left when `x` is empty. A single step either moves the head right, in which case one symbol is pushed onto `x` and the head consumes one symbol of `y`, leaving the total unchanged, or moves the head left, in which case one symbol is popped from `x` and one is pushed onto `y`, increasing the total by one; when `x` is empty the head writes a blank and one symbol is pushed onto `y`, again increasing the total by one. A halting configuration is a fixed point of the step, so the total does not change. Hence one step increases `x.length + y.length` by at most one. This is the size invariant from which any statement about how much a computation of n steps can write follows, and in particular it bounds the length of the output of a polynomial-time computation.
-- source:
--   Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix (the one-tape machine, the four cases of a step)

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

variable {Γ : Type} {Q : Type} (M : TM Γ)

theorem tm_step_tape_len (c : Cfg Γ M.Q) :
    (M.step c).left.length + (M.step c).right.length ≤ c.left.length + c.right.length + 1 := by
  sorry

end CookPvsNP
