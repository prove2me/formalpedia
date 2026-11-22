-- Prove2me | Theorems.Thm_Comp_fixAux_eq_iterate
-- name    : Comp.fixAux_eq_iterate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:46:27.764039+00:00
-- url     : https://prove2.me/theorems/34eae8df-b34f-403e-97eb-a6a8b12b4c4c
-- title:
--   Comp: fix Aux eq iterate
-- statement:
--   **The loop is exactly the `n`-th iterate.** The early exit does not change *what* is computed,
--       only how much of it is unfolded: once `f x = x` every later iterate is `x` too. Unconditional,
--       and it is what lets facts about `Function.iterate` transfer to `fixFrom` without reasoning
--       about where the loop stopped.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L83-L96
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L83-L96

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]

theorem Comp.fixAux_eq_iterate (f : Finset S → Finset S) (n : ℕ) (x : Finset S) :
    fixAux f n x = f^[n] x := by sorry
