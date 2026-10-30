-- Prove2me | Theorems.Thm_BitcoinPenalty_htlc_cheater_one_block_anchors
-- name    : BitcoinPenalty.htlc_cheater_one_block_anchors
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:55:26.883053+00:00
-- url     : https://prove2.me/theorems/04310c37-d501-4184-8ab9-ca7cecc31dd4
-- title:
--   The cheater's HTLC spend waits one block (anchors)
-- statement:
--   Under the safety hypotheses and the `CSV` flag: version at least 2, disable bit clear, `nSequence ≥ 1`.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinSig
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.htlc_cheater_one_block_anchors (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K) (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytesAnchors K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytesAnchors K h)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytesAnchors K h))
      (ws ++ [BitcoinPenalty.offeredBytesAnchors K h]) = true) :
    2 ≤ c.tx.version ∧
      BitcoinToLocal.inputSequence c.tx c.nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 ∧
      1 ≤ BitcoinToLocal.inputSequence c.tx c.nIn := by sorry
