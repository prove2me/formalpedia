-- Prove2me | Theorems.Thm_BitcoinPenalty_cheater_needs_delay
-- name    : BitcoinPenalty.cheater_needs_delay
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:54:05.784715+00:00
-- url     : https://prove2.me/theorems/ca632e78-482c-4fc8-8396-7f8698a3ec5f
-- title:
--   The cheater cannot spend to_local early
-- statement:
--   Under `NoRevocationSig` and the `CSV` flag: no accepted spend has version below 2 or `nSequence` below `toSelfDelay`.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinToLocal
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.cheater_needs_delay (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (ws ++ [BitcoinPenalty.toLocalBytes K]) = true) :
    ¬ (c.tx.version < 2 ∨ BitcoinToLocal.inputSequence c.tx c.nIn < K.toSelfDelay.toNat) := by sorry
