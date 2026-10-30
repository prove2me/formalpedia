-- Prove2me | Theorems.Thm_BitcoinAnchors_to_remote_p2wsh_spend
-- name    : BitcoinAnchors.to_remote_p2wsh_spend
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:16:27.128856+00:00
-- url     : https://prove2.me/theorems/6ad7cdcd-000c-47fc-bffa-32ebae3b649d
-- title:
--   The to_remote output under VerifyScript
-- statement:
--   With the `WITNESS` flag and a key of at most 520 bytes, any witness `ws`: `verifyScript` accepts `ws ++ [toRemoteBytes k]` for the P2WSH program of `toRemoteBytes k` iff the program is true, every element is at most 520 bytes, and `ToRemoteSpend` holds for the context's flags and `legacyOracle` on `ws.reverse`. The remote balance is spendable by the remote key only after one block (the CSV that makes anchors' fee-bumping safe).
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.to_remote_p2wsh_spend (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (remoteKey : Bytes) (ws : List Bytes)
    (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c []
        (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinAnchors.toRemoteBytes remoteKey)))
        (ws ++ [BitcoinAnchors.toRemoteBytes remoteKey]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.toRemoteBytes remoteKey)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      BitcoinAnchors.ToRemoteSpend (BitcoinVerify.scriptFlagsOf c.flags)
        (BitcoinSig.legacyOracle (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
          (BitcoinAnchors.toRemoteBytes remoteKey))
        remoteKey ws.reverse := by sorry
