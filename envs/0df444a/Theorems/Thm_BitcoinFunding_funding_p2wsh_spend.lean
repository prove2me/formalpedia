-- Prove2me | Theorems.Thm_BitcoinFunding_funding_p2wsh_spend
-- name    : BitcoinFunding.funding_p2wsh_spend
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:40:05.040029+00:00
-- url     : https://prove2.me/theorems/9b1bcb2d-cbd5-45f4-8b2f-e838509d2bd5
-- title:
--   The funding output under VerifyScript: the channel's funds move only with both signatures
-- statement:
--   For a context with the `WITNESS` flag, keys of at most 520 bytes and any witness `ws`: `verifyScript tap c [] (witnessBytes 0 (sha256 (fundingBytes pubkey1 pubkey2))) (ws ++ [fundingBytes pubkey1 pubkey2]) = true` iff the program is a true value, every witness element is at most 520 bytes, and `FundingSpend` holds for the context's flags and the signature mission's `legacyOracle` of its transaction on `ws.reverse`. With the `to_local`, HTLC and anchor missions this completes the script set of a Lightning channel's on-chain life: funding, commitment outputs, HTLCs, anchors.
-- source:
--   BOLT #3, Funding Transaction Output: https://github.com/lightning/bolts/blob/master/03-transactions.md#funding-transaction-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKMULTISIG), ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP141, BIP147

import Definitions.Def_BitcoinFunding
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinFunding BitcoinHtlc
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinFunding.funding_p2wsh_spend (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (pubkey1 pubkey2 : Bytes) (ws : List Bytes)
    (h1 : pubkey1.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (h2 : pubkey2.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinFunding.fundingBytes pubkey1 pubkey2)))
        (ws ++ [BitcoinFunding.fundingBytes pubkey1 pubkey2]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinFunding.fundingBytes pubkey1 pubkey2)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      BitcoinFunding.FundingSpend (BitcoinVerify.scriptFlagsOf c.flags)
        (BitcoinSig.legacyOracle (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 (BitcoinFunding.fundingBytes pubkey1 pubkey2))
        pubkey1 pubkey2 ws.reverse := by sorry
