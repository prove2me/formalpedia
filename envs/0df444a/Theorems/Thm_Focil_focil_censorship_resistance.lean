-- Prove2me | Theorems.Thm_Focil_focil_censorship_resistance
-- name    : Focil.focil_censorship_resistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:38:17.372404+00:00
-- url     : https://prove2.me/theorems/9d3affda-0ccf-46d3-819d-fc840ffbba7f
-- title:
--   Focil: focil censorship resistance
-- statement:
--   **Per-IL censorship resistance.**
--
--     Building block for the headline 1-of-N theorem
--     (`focil_one_of_n_protection` below). Given an *explicit*
--     witness IL, this theorem says the transaction must be in the
--     canonical block.
--
--     Hypotheses:
--
--     - `h_tx_in_il`:        `tx` is in inclusion list `il`.
--     - `h_il_stored`:       `il` is in `fc.state.stored_ils`.
--     - `h_il_considered`:   `il`'s author is not in
--                            `fc.state.equivocators` (so attesters
--                            consider this IL).
--     - `h_can_append`:      `tx` could be validly appended to `b`'s
--                            end-state (`CanAppend tx b`).
--     - `h_block_not_full`:  `b` does not satisfy `fc.full`.
--     - `h_canonical`:       `b` is the canonical chain head under
--                            the fork-choice rule `fc`.
--
--     Conclusion: `tx ∈ b.transactions`.
--
--     Note: `h_il_considered` is "not yet observed equivocating,"
--     not "honest in the colloquial sense" (FINDINGS.md §2.4).
--
--   Source: https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Safety.lean#L85-L102
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/Safety.lean#L85-L102

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Definitions.Def_Focil_Helpers
import Definitions.Def_Focil_Safety
set_option autoImplicit false
open Focil

theorem Focil.focil_censorship_resistance
    (fc : ForkChoice) (b : Block) (il : InclusionList) (tx : Transaction)
    (h_tx_in_il      : tx ∈ il.transactions)
    (h_il_stored     : il ∈ fc.state.stored_ils)
    (h_il_considered : IsConsidered fc.state il)
    (h_can_append    : fc.canAppend tx b)
    (h_block_not_full: ¬ fc.full b)
    (h_canonical     : IsCanonical fc b) :
    tx ∈ b.transactions := by sorry
