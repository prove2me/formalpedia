-- Prove2me | Theorems.Thm_Comp_fixAux_fixed_of_card_le
-- name    : Comp.fixAux_fixed_of_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:12:07.595676+00:00
-- url     : https://prove2.me/theorems/04c44d3e-08eb-4142-b8c1-e50f6a42a7a7
-- title:
--   Comp: fix Aux fixed of card le
-- statement:
--   **A descending chain stops within `x.card` steps.** The invariant is `x.card ≤ n`: a step that
--       changes anything is strict, so it costs at least one from the cardinality, and at `n = 0` the
--       region is empty, where `f x ⊆ x` leaves `f x = x` the only option.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L202-L218
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L202-L218

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]

theorem Comp.fixAux_fixed_of_card_le (f : Finset S → Finset S) (hmono : Monotone f) (n : ℕ)
    (x : Finset S) (hx : f x ≤ x) (hcard : x.card ≤ n) :
    f (fixAux f n x) = fixAux f n x := by sorry
