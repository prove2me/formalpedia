-- Prove2me | Theorems.Thm_Focil_front_running_breaks_appendability
-- name    : Focil.front_running_breaks_appendability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:37:43.716714+00:00
-- url     : https://prove2.me/theorems/02f6e530-a243-4302-b8ea-ef93bc5fda2e
-- title:
--   Focil: front running breaks appendability
-- statement:
--   **Front-running breaks appendability (FINDINGS §2.3).**
--
--     Given:
--
--     - A block `b` to which an IL transaction `tx_il` is
--       appendable (under the nonce-only model).
--     - An "evil" transaction `tx_evil` sharing `tx_il`'s sender,
--       also appendable to `b`.
--
--     Then: the extension `b ++ [tx_evil]` makes `tx_il` no longer
--     appendable.
--
--     This formalizes the nonce-front-running attack: a colluding
--     party submits a transaction with the same `(sender, nonce)`
--     as an IL-listed transaction, the proposer appends it to the
--     block, and the IL transaction's nonce is now stale. The
--     proposer can then legitimately invoke EIP-7805's
--     conditional-inclusion exemption (`¬ CanAppend tx_il b'`).
--
--     Note that we do *not* need to explicitly assume that
--     `tx_evil` and `tx_il` share a nonce: the same-sender
--     hypothesis combined with both being appendable to the same
--     state already forces nonce collision (both must equal the
--     state's expected nonce for that sender). The hypothesis set
--     is therefore minimal: same sender plus simultaneous
--     appendability is sufficient to expose the attack.
--
--     This theorem does *not* contradict the main safety theorem.
--     The safety theorem takes `h_can_append` as a hypothesis;
--     this theorem says "the hypothesis can be made false by an
--     adversary who picks `b'` adversarially." The two theorems
--     are about different layers (safety conditional on
--     appendability vs. how appendability behaves under
--     adversarial block construction). The attack surface they
--     jointly characterize is exactly what FINDINGS §2.3
--     describes.
--
--   Source: https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/AccountState.lean#L236-L261
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/AccountState.lean#L236-L261

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_AccountState
set_option autoImplicit false
open Focil

theorem Focil.front_running_breaks_appendability
    (initial : AccountState)
    (b : Block)
    (tx_il tx_evil : Transaction)
    (h_same_sender    : tx_evil.sender = tx_il.sender)
    (h_il_appendable  : canAppendToBlock initial b tx_il)
    (h_evil_appendable: canAppendToBlock initial b tx_evil) :
    ¬ canAppendToBlock initial
        { b with transactions := b.transactions ++ [tx_evil] }
        tx_il := by sorry
