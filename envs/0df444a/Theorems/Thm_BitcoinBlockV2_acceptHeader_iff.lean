-- Prove2me | Theorems.Thm_BitcoinBlockV2_acceptHeader_iff
-- name    : BitcoinBlockV2.acceptHeader_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:00:20.019019+00:00
-- url     : https://prove2.me/theorems/8b19018b-d0ff-4c6b-b92c-67bf77a4c4b2
-- title:
--   The header path is the Header mission's contextual check
-- statement:
--   `acceptHeader S h now = accept S []` iff the proof of work holds, `h.prevBlock` is the tip's hash, and the Header mission's `contextualCheck` holds with the chain's tip height, times, required bits and the clock.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader

theorem BitcoinBlockV2.acceptHeader_iff (S : ChainState) (h : BitcoinSer.Header) (now : Int) :
    BitcoinBlockV2.acceptHeader S h now = .accept S [] ↔
      BitcoinBlockV2.checkHeaderPow h = true ∧ h.prevBlock = S.tipHash ∧
      BitcoinHeader.contextualCheck ⟨h.version, (h.time : Int), BitVec.ofNat 32 h.bits⟩ S.tipHeight
        (S.timesTo S.tipHeight) S.requiredBits now = true := by sorry
