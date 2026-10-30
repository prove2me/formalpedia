-- Prove2me | Theorems.Thm_BitcoinAnchors_anchor_anyone_delay
-- name    : BitcoinAnchors.anchor_anyone_delay
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:17:21.877174+00:00
-- url     : https://prove2.me/theorems/98d9af81-2db9-4af6-95de-d8a18075447d
-- title:
--   Anyone can spend the anchor after 16 blocks, in transaction terms
-- statement:
--   Additionally for an input with flag-free `nSequence` below $2^{16}$: the empty-signature witness verifies iff the program is true, the transaction is version 2 or later, and `nSequence ≥ 16`. The anchor's "anyone can sweep it after 16 blocks" property, as consensus enforces it.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinSer
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.anchor_anyone_delay (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (fundingKey : Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hseq : BitcoinToLocal.inputSequence c.tx c.nIn < 2 ^ 16) :
    BitcoinVerify.verifyScript tap c []
        (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fundingKey)))
        [[], BitcoinAnchors.anchorBytes fundingKey] = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fundingKey)) = true ∧
      2 ≤ c.tx.version ∧ 16 ≤ BitcoinToLocal.inputSequence c.tx c.nIn := by sorry
