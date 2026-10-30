-- Prove2me | Theorems.Thm_BitcoinHtlc_offered_p2wsh_spend
-- name    : BitcoinHtlc.offered_p2wsh_spend
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:28:47.765398+00:00
-- url     : https://prove2.me/theorems/97fb76d2-2fc8-4e3a-a052-019f8edaf473
-- title:
--   The offered HTLC output under VerifyScript
-- statement:
--   For a context with the `WITNESS` flag and pushed strings of at most 520 bytes, any witness `ws`: `verifyScript tap c [] (witnessBytes 0 (sha256 (offeredBytes …))) (ws ++ [offeredBytes …]) = true` iff the program is a true value, every witness element is at most 520 bytes, and `OfferedSpend` holds for the flags of $c$ and the signature mission's `legacyOracle` of $c$'s transaction on the reversed witness. So the output is spent only by the revocation key, by the remote key with the payment preimage, or by both HTLC keys on the timeout transaction.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.offered_p2wsh_spend (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (revHash remoteKey localKey payHash : Bytes) (ws : List Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c []
        (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinHtlc.offeredBytes revHash remoteKey localKey payHash)))
        (ws ++ [BitcoinHtlc.offeredBytes revHash remoteKey localKey payHash]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinHtlc.offeredBytes revHash remoteKey localKey payHash)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      BitcoinHtlc.OfferedSpend (BitcoinVerify.scriptFlagsOf c.flags)
        (BitcoinSig.legacyOracle (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
          (BitcoinHtlc.offeredBytes revHash remoteKey localKey payHash))
        revHash remoteKey localKey payHash ws.reverse := by sorry
