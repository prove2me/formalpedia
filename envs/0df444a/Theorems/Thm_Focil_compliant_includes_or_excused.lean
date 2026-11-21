-- Prove2me | Theorems.Thm_Focil_compliant_includes_or_excused
-- name    : Focil.compliant_includes_or_excused
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:37:44.473497+00:00
-- url     : https://prove2.me/theorems/65fabfdb-e593-42ac-b778-d376d6801851
-- title:
--   Focil: compliant includes or excused
-- statement:
--   Direct unfolding of `FocilCompliant` at a specific
--     (IL, transaction) pair.
--
--     The safety theorem in `Focil/Safety.lean` uses this exact
--     calling convention; stating it as a lemma makes that proof read
--     more cleanly.
--
--   Source: https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Protocol.lean#L181-L190
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Protocol.lean#L181-L190

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
set_option autoImplicit false
open Focil

theorem Focil.compliant_includes_or_excused
    {canAppend : Transaction → Block → Prop}
    {full : Block → Prop} {b : Block} {state : FocilState}
    {il : InclusionList} {tx : Transaction}
    (hCompl : FocilCompliant canAppend full b state)
    (hIl    : il ∈ state.stored_ils)
    (hConsidered : IsConsidered state il)
    (hTx    : tx ∈ il.transactions) :
    tx ∈ b.transactions ∨ ¬ canAppend tx b ∨ full b := by sorry
