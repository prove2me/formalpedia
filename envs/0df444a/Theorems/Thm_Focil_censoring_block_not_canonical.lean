-- Prove2me | Theorems.Thm_Focil_censoring_block_not_canonical
-- name    : Focil.censoring_block_not_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:38:18.204162+00:00
-- url     : https://prove2.me/theorems/54c7716e-40ed-450b-accb-8413dba453fb
-- title:
--   Focil: censoring block not canonical
-- statement:
--   **Contrapositive corollary** of `focil_censorship_resistance`.
--
--     Reading: a candidate block `b` that omits a transaction `tx`
--     satisfying the standard inclusion preconditions cannot become
--     the canonical chain head.
--
--     This is the form a builder reasoning about block construction
--     cares about: "if I exclude this transaction, my block gets
--     orphaned by the fork-choice rule."
--
--   Source: https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Safety.lean#L177-L190
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Safety.lean#L177-L190

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Definitions.Def_Focil_Helpers
import Definitions.Def_Focil_Safety
set_option autoImplicit false
open Focil

theorem Focil.censoring_block_not_canonical
    (fc : ForkChoice) (b : Block) (il : InclusionList) (tx : Transaction)
    (h_tx_in_il      : tx ∈ il.transactions)
    (h_il_stored     : il ∈ fc.state.stored_ils)
    (h_il_considered : IsConsidered fc.state il)
    (h_can_append    : fc.canAppend tx b)
    (h_block_not_full: ¬ fc.full b)
    (h_tx_excluded   : tx ∉ b.transactions) :
    ¬ IsCanonical fc b := by sorry
