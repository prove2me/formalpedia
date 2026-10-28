-- Prove2me | Theorems.Thm_BitcoinBlockV2_futureTime_iff
-- name    : BitcoinBlockV2.futureTime_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:01:05.123184+00:00
-- url     : https://prove2.me/theorems/98d2c82c-d4cc-4970-bd18-cac6cc722932
-- title:
--   BLOCK_TIME_FUTURE characterized
-- statement:
--   `validate S b now = futureTime` iff the proof of work holds, the parent is the tip, the bits are the required ones, the time exceeds the median time past, and $now + 7200 < time$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.futureTime_iff (S : ChainState) (b : BitcoinSer.Block) (now : Int) :
    BitcoinBlockV2.validate S b now = .futureTime ↔
      BitcoinBlockV2.checkHeaderPow b.header = true ∧ b.header.prevBlock = S.tipHash ∧
      BitVec.ofNat 32 b.header.bits = S.requiredBits ∧ S.mtp < (b.header.time : Int) ∧
      now + MAX_FUTURE_BLOCK_TIME < (b.header.time : Int) := by sorry
