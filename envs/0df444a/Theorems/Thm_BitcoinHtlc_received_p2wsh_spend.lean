-- Prove2me | Theorems.Thm_BitcoinHtlc_received_p2wsh_spend
-- name    : BitcoinHtlc.received_p2wsh_spend
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:28:58.966349+00:00
-- url     : https://prove2.me/theorems/080c5c2b-093d-43fc-8d77-4bf86808a035
-- title:
--   The received HTLC output under VerifyScript
-- statement:
--   As `offered_p2wsh_spend` for the received script with $|{\rm expiry}| < 2^{32}$: the output is spent only by the revocation key, by both HTLC keys with the payment preimage on the success transaction, or by the remote key after the lock time. Together with the `to_local` mission this covers every script of a BOLT #3 commitment transaction (non-anchor form).
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.received_p2wsh_spend (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (revHash remoteKey localKey payHash : Bytes) (expiry : Int) (ws : List Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) :
    BitcoinVerify.verifyScript tap c []
        (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry)))
        (ws ++ [BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      BitcoinHtlc.ReceivedSpend (BitcoinVerify.scriptFlagsOf c.flags)
        (BitcoinSig.legacyOracle (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
          (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry))
        revHash remoteKey localKey payHash expiry ws.reverse := by sorry
