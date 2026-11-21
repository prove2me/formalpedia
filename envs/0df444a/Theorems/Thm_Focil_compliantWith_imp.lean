-- Prove2me | Theorems.Thm_Focil_compliantWith_imp
-- name    : Focil.compliantWith_imp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:38:03.87919+00:00
-- url     : https://prove2.me/theorems/28b00026-565a-4ecd-a30f-77cc845f1649
-- title:
--   Focil: compliant With imp
-- statement:
--   Plain unfolding of `CompliantWith` at a single transaction.
--
--     Stating this as a named lemma rather than inlining the
--     unfolding makes downstream proofs read more naturally.
--
--   Source: https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Helpers.lean#L21-L28
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Helpers.lean#L21-L28

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_Helpers
set_option autoImplicit false
open Focil

theorem Focil.compliantWith_imp
    {canAppend : Transaction → Block → Prop}
    {full : Block → Prop} {b : Block} {il : InclusionList}
    {tx : Transaction}
    (h : CompliantWith canAppend full b il)
    (htx : tx ∈ il.transactions) :
    tx ∈ b.transactions ∨ ¬ canAppend tx b ∨ full b := by sorry
