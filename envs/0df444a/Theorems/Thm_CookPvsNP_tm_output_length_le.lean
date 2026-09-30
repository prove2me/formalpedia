-- Prove2me | Theorems.Thm_CookPvsNP_tm_output_length_le
-- name    : CookPvsNP.tm_output_length_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T06:44:13.638376+00:00
-- url     : https://prove2.me/theorems/8b233c5d-cee7-43f1-b8fa-823fbc614cbd
-- title:
--   A run of n steps on input w produces output of length at most n + |w| + 1
-- statement:
--   In the one-tape model of Cook's Appendix the tape to the left of the head is a list stored in reverse order and the tape is extended implicitly by blanks, so a single step can enlarge the part of the tape that carries information by at most one square: a step either pushes one symbol onto the left part, or moves one symbol from the right part to the left part, or pushes one symbol onto the right part. Starting from the initial configuration, whose two parts together hold at most the |w| symbols of the input, after n steps the head and the part to its right therefore hold at most n + |w| + 1 squares. The output of a configuration is exactly the part read from the head rightwards with trailing blanks removed, so it is no longer than that. This is the size estimate on which any polynomial-time bound rests: a computation of polynomially many steps can only write polynomially many output symbols, which is what makes the time bounds of composed machines composable.
-- source:
--   Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix (the one-tape machine) and §1 p. 2, the running-time clause of Definition 3

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

variable {Γ : Type} {Q : Type} (M : TM Γ)

theorem tm_output_length_le (n : ℕ) (w : List Γ) :
    (M.output (M.run n (M.init w))).length ≤ n + w.length + 1 := by
  sorry

end CookPvsNP
