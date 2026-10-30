-- Prove2me | Theorems.Thm_BitcoinPenalty_penalty_any_block
-- name    : BitcoinPenalty.penalty_any_block
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:55:51.852044+00:00
-- url     : https://prove2.me/theorems/f2a7845e-4eba-43c5-8878-0cae79866485
-- title:
--   The penalty is valid in any block
-- statement:
--   The `to_local` penalty witness is accepted with no condition on the transaction, and with `nLockTime = 0` the penalty transaction is final at every height: the honest party wins the race whenever it gets a transaction confirmed within the delay.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.penalty_any_block (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.toLocalBytes K)) = true)
    (sigR : BitcoinSer.Bytes) (hlen : sigR.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hsig : (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)).checkSig sigR K.revPk = some true)
    (hlock : c.tx.nLockTime = 0) (height : Nat) (blockTime : Int) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
        (BitcoinPenalty.toLocalPenaltyWitness K sigR) = true ∧
      BitcoinBlockV2.isFinalTx c.tx height blockTime = true := by sorry
