-- Prove2me | Theorems.Thm_BitcoinBlockV2_futureTime_transient
-- name    : BitcoinBlockV2.futureTime_transient
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:02:45.155157+00:00
-- url     : https://prove2.me/theorems/76ad7a27-4c2c-4995-a824-50844aa1e00d
-- title:
--   A future-time rejection is transient
-- statement:
--   If `validate S b now = futureTime`, then for every $now' \ge time - 7200$ the outcome is not `futureTime`, and it equals the outcome at clock $time - 7200$: the block is not permanently invalidated by its time.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.futureTime_transient (S : ChainState) (b : BitcoinSer.Block) (now : Int)
    (h : BitcoinBlockV2.validate S b now = .futureTime) (now' : Int)
    (hle : (b.header.time : Int) ≤ now' + MAX_FUTURE_BLOCK_TIME) :
    BitcoinBlockV2.validate S b now' ≠ .futureTime ∧
    BitcoinBlockV2.validate S b now' = BitcoinBlockV2.validate S b ((b.header.time : Int) - MAX_FUTURE_BLOCK_TIME) := by sorry
