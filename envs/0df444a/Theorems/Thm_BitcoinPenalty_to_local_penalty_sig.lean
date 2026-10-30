-- Prove2me | Theorems.Thm_BitcoinPenalty_to_local_penalty_sig
-- name    : BitcoinPenalty.to_local_penalty_sig
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:51:14.386531+00:00
-- url     : https://prove2.me/theorems/7200c120-06f3-43da-a5b2-95263dc92f45
-- title:
--   to_local: the revocation witness is accepted with no delay
-- statement:
--   For a well-formed `K`, a true program and any accepted signature `sigR` (≤ 520 bytes) for `revPk`: `verifyScript tap c [] (p2wshOf (toLocalBytes K)) (toLocalPenaltyWitness K sigR) = true`, with no hypothesis on the transaction's version, `nSequence` or lock time, nor on the `CSV` flag.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.to_local_penalty_sig (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.toLocalBytes K)) = true)
    (sigR : BitcoinSer.Bytes) (hlen : sigR.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hsig : (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)).checkSig sigR K.revPk = some true) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (BitcoinPenalty.toLocalPenaltyWitness K sigR) = true := by sorry
