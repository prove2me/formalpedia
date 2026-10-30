-- Prove2me | Theorems.Thm_BitcoinPenalty_cheater_delay_in_tx_terms
-- name    : BitcoinPenalty.cheater_delay_in_tx_terms
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:53:40.237388+00:00
-- url     : https://prove2.me/theorems/1565daef-e583-43c0-aa31-fa5d004e24a6
-- title:
--   The cheater's to_local spend needs version 2 and nSequence ≥ to_self_delay
-- statement:
--   Under `NoRevocationSig`, the `CSV` flag and flag-free `nSequence`: any accepted spend has `2 ≤ version` and `toSelfDelay ≤ nSequence`.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinToLocal
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.cheater_delay_in_tx_terms (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (ws ++ [BitcoinPenalty.toLocalBytes K]) = true)
    (hseq : BitcoinToLocal.inputSequence c.tx c.nIn < 2 ^ 16) :
    2 ≤ c.tx.version ∧ K.toSelfDelay.toNat ≤ BitcoinToLocal.inputSequence c.tx c.nIn := by sorry
