-- Prove2me | Theorems.Thm_Comp_fixFrom_univ_fixed
-- name    : Comp.fixFrom_univ_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:14:01.279427+00:00
-- url     : https://prove2.me/theorems/8802b058-bd14-4484-9539-aa1c1800d264
-- title:
--   Comp: fix From univ fixed
-- statement:
--   The loop from `⊤` always stops at a fixed point. The fuel is `Fintype.card S`, which is exactly
--       `Finset.univ.card`, so the invariant holds at the start and the previous lemma does the rest.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L246-L248
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/FixLoop.lean#L246-L248

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]

theorem Comp.fixFrom_univ_fixed (f : Finset S → Finset S) (hmono : Monotone f) :
    f (fixFrom f Finset.univ) = fixFrom f Finset.univ := by sorry
