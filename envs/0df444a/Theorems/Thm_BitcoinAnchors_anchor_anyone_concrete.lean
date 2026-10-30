-- Prove2me | Theorems.Thm_BitcoinAnchors_anchor_anyone_concrete
-- name    : BitcoinAnchors.anchor_anyone_concrete
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:17:11.09304+00:00
-- url     : https://prove2.me/theorems/722552cb-c781-4e67-ae57-81f89c73990c
-- title:
--   Anyone can spend the anchor after the delay: the empty-signature witness under the concrete checker
-- statement:
--   With the `WITNESS` and `CHECKSEQUENCEVERIFY` flags and a funding key of at most 520 bytes: `verifyScript tap c [] (witnessBytes 0 (sha256 (anchorBytes k))) [[], anchorBytes k] = true ↔ castToBool (sha256 (anchorBytes k)) = true ∧ checkSequence c.tx c.nIn 16 = true`. The empty signature is a clean false under consensus flags (the signature mission's `checkSig_empty`; no pubkey-encoding hypothesis is needed since `WITNESS_PUBKEYTYPE` is policy), so the spend reduces to Core's `CheckSequence` with operand 16.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.anchor_anyone_concrete (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (fundingKey : Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c []
        (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fundingKey)))
        [[], BitcoinAnchors.anchorBytes fundingKey] = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fundingKey)) = true ∧
      BitcoinSig.checkSequence c.tx c.nIn 16 = true := by sorry
