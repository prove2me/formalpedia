-- Prove2me | Theorems.Thm_Comp_fixAux_fixed_of_compl_card_le
-- name    : Comp.fixAux_fixed_of_compl_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:13:57.982032+00:00
-- url     : https://prove2.me/theorems/cd89572f-d47d-4d6f-9ed9-557c4908d7e1
-- title:
--   Comp: fix Aux fixed of compl card le
-- statement:
--   **The dual: an ascending chain stops within `card S - x.card` steps.** Same argument against the
--       complement, and at `n = 0` the region is everything.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L222-L242
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L222-L242

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]

theorem Comp.fixAux_fixed_of_compl_card_le (f : Finset S → Finset S) (hmono : Monotone f) (n : ℕ)
    (x : Finset S) (hx : x ≤ f x) (hcard : Fintype.card S - x.card ≤ n) :
    f (fixAux f n x) = fixAux f n x := by sorry
