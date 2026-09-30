-- Prove2me | Theorems.Thm_CookPvsNP_tm_run_tape_len
-- name    : CookPvsNP.tm_run_tape_len
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T07:04:15.529973+00:00
-- url     : https://prove2.me/theorems/9d55c3c8-3b45-4c36-a8c2-aa6581cf8a5b
-- title:
--   A run of n steps grows the total tape by at most n squares
-- statement:
--   By induction on the number of steps, using the one-step size invariant that a step increases `left.length + right.length` by at most one, a computation of n steps starting from a configuration `c` ends in a configuration whose two parts together hold at most `n + c.left.length + c.right.length` squares. Since the output of a configuration is the part read from the head rightwards with trailing blanks removed, it is no longer than the head plus the right part, and therefore the output of a run of n steps from the initial configuration on input `w`, whose two parts hold at most `|w|` squares, has length at most `n + |w| + 1`. This is the size estimate that makes the time bounds of composed machines composable: a first machine running polynomially many steps can only write polynomially many output symbols, which bounds the input length that the second machine must handle.
-- source:
--   Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix (the one-tape machine) and §1 p. 2, the running-time clause of Definition 3

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

variable {Γ : Type} {Q : Type} (M : TM Γ)

theorem tm_run_tape_len (n : ℕ) (c : Cfg Γ M.Q) :
    (M.run n c).left.length + (M.run n c).right.length ≤ n + c.left.length + c.right.length := by
  sorry

end CookPvsNP
