-- Prove2me | Theorems.Thm_BitcoinPenalty_to_remote_honest_only
-- name    : BitcoinPenalty.to_remote_honest_only
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T22:52:42.450037+00:00
-- url     : https://prove2.me/theorems/a86a24dc-c361-4d5a-975e-fdef7539a1e9
-- title:
--   to_remote (anchors): only the remote key spends it, after one block
-- statement:
--   Accepted witnesses for `toRemoteBytes K` are exactly `[sig]` with `sig` valid for `remoteKey` and `CsvPasses … 1`; the broadcaster has no path.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.to_remote_honest_only (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (ws : List BitcoinSer.Bytes) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toRemoteBytes K))
        (ws ++ [BitcoinPenalty.toRemoteBytes K]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.toRemoteBytes K)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      ∃ sig, ws = [sig] ∧
        (BitcoinPenalty.oracleOf c (BitcoinPenalty.toRemoteBytes K)).checkSig sig K.remoteKey = some true ∧
        BitcoinToLocal.CsvPasses (BitcoinVerify.scriptFlagsOf c.flags)
          (BitcoinPenalty.oracleOf c (BitcoinPenalty.toRemoteBytes K)) 1 := by sorry
