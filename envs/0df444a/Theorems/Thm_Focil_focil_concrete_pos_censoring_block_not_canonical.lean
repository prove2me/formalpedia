-- Prove2me | Theorems.Thm_Focil_focil_concrete_pos_censoring_block_not_canonical
-- name    : Focil.focil_concrete_pos_censoring_block_not_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:38:47.964423+00:00
-- url     : https://prove2.me/theorems/e472f834-055d-4686-84bd-98a653711b96
-- title:
--   Focil: focil concrete pos censoring block not canonical
-- statement:
--   **Concrete builder-side contrapositive.**
--
--     The contrapositive of `focil_concrete_pos_safety`: a block
--     that omits an IL transaction whose nonce concretely matches
--     the sender's next-expected nonce (against
--     `AccountState.initial`) cannot become the canonical chain
--     head under the PoS-derived `ForkChoice`.
--
--     Useful as a builder-incentive statement at full
--     concreteness: "if I propose a block that omits a
--     nonce-valid IL transaction, my block is orphaned by the
--     fork-choice rule." Every hypothesis is decidable on
--     concrete account-state data; no opaque predicate appears.
--
--   Source: https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/EndToEnd.lean#L239-L257
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/EndToEnd.lean#L239-L257

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice
import Definitions.Def_Focil_Helpers
import Definitions.Def_Focil_Safety
import Definitions.Def_Focil_StakeModel
import Definitions.Def_Focil_AccountState
import Definitions.Def_Focil_EndToEnd
set_option autoImplicit false
open Focil

theorem Focil.focil_concrete_pos_censoring_block_not_canonical
    {s : StakeModel} (r : AttesterRun s)
    (b : Block) (tx : Transaction)
    (initial : AccountState)
    (h_canAppend_pin :
      r.canAppend = fun tx' b' => canAppendToBlock initial b' tx')
    (h_listed_by_some_honest_member :
      ∃ il, il ∈ r.state.stored_ils
            ∧ IsConsidered r.state il
            ∧ tx ∈ il.transactions)
    (h_can_append    : canAppendToBlock initial b tx)
    (h_block_not_full: ¬ r.full b)
    (h_tx_excluded   : tx ∉ b.transactions) :
    ¬ IsCanonical r.toForkChoice b := by sorry
