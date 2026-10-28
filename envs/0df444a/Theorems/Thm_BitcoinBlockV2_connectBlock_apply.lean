-- Prove2me | Theorems.Thm_BitcoinBlockV2_connectBlock_apply
-- name    : BitcoinBlockV2.connectBlock_apply
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:10:43.277989+00:00
-- url     : https://prove2.me/theorems/547ce25d-3583-4371-ae44-8db94df477e9
-- title:
--   ConnectBlock computes the declarative ledger
-- statement:
--   `connectBlock S b = some (u, undo)` implies `u = (applySpec S b).utxo`: the ledger after the source loop is the fold of `UpdateCoins` over the block's transactions (or unchanged for the genesis).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.connectBlock_apply (S : ChainState) (b : BitcoinSer.Block) (u : Ledger) (undo : BlockUndo)
    (h : BitcoinBlockV2.connectBlock S b = some (u, undo)) : u = (BitcoinBlockV2.applySpec S b).utxo := by sorry
