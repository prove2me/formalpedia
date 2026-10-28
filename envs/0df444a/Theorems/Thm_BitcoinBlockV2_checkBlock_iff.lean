-- Prove2me | Theorems.Thm_BitcoinBlockV2_checkBlock_iff
-- name    : BitcoinBlockV2.checkBlock_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:04:20.208577+00:00
-- url     : https://prove2.me/theorems/87433cdf-5048-4c36-b72b-9c743c42f508
-- title:
--   CheckBlock characterized
-- statement:
--   `checkBlock b = true` iff the proof of work holds and `BlockSpec b`: non-empty, merkle root matching and unmutated, size limits, exactly the first transaction a coinbase, every transaction well formed, legacy sigops within 80,000.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.checkBlock_iff (b : BitcoinSer.Block) :
    BitcoinBlockV2.checkBlock b = true ↔ BitcoinBlockV2.checkHeaderPow b.header = true ∧ BitcoinBlockV2.BlockSpec b := by sorry
