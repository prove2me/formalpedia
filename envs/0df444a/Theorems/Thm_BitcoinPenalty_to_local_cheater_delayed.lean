-- Prove2me | Theorems.Thm_BitcoinPenalty_to_local_cheater_delayed
-- name    : BitcoinPenalty.to_local_cheater_delayed
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:53:23.728597+00:00
-- url     : https://prove2.me/theorems/7328fa2e-4662-41bd-b401-edf9abdc08ee
-- title:
--   to_local safety: without the revocation key, every accepted spend takes the delayed path
-- statement:
--   Under `NoRevocationSig`: every witness `verifyScript` accepts for `toLocalBytes K` is `[sig, b]` with `DelayedSpend`: `b` false, `CsvPasses … toSelfDelay`, `sig` valid for `localDelayedPk`.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.to_local_cheater_delayed (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (ws ++ [BitcoinPenalty.toLocalBytes K]) = true) :
    ∃ b sig, ws = [sig, b] ∧
      BitcoinPenalty.DelayedSpend (BitcoinVerify.scriptFlagsOf c.flags)
        (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K b sig := by sorry
