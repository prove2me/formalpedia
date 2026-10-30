-- Prove2me | Theorems.Thm_BitcoinAnchors_received_p2wsh_spend
-- name    : BitcoinAnchors.received_p2wsh_spend
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:17:00.619311+00:00
-- url     : https://prove2.me/theorems/47ebaed2-1167-4bb9-afc6-43d7069aa065
-- title:
--   The received HTLC output (anchors) under VerifyScript
-- statement:
--   As above with `ReceivedSpend` and $|{\rm expiry}| < 2^{32}$. With the `to_local` and HTLC missions this covers every script of a BOLT #3 commitment transaction in both the legacy and the anchors form.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.received_p2wsh_spend (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (revHash remoteKey localKey payHash : Bytes) (expiry : Int) (ws : List Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) :
    BitcoinVerify.verifyScript tap c []
        (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinAnchors.receivedBytes revHash remoteKey localKey payHash expiry)))
        (ws ++ [BitcoinAnchors.receivedBytes revHash remoteKey localKey payHash expiry]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.receivedBytes revHash remoteKey localKey payHash expiry)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      BitcoinAnchors.ReceivedSpend (BitcoinVerify.scriptFlagsOf c.flags)
        (BitcoinSig.legacyOracle (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
          (BitcoinAnchors.receivedBytes revHash remoteKey localKey payHash expiry))
        revHash remoteKey localKey payHash expiry ws.reverse := by sorry
