-- Prove2me | Theorems.Thm_BitcoinBlockV2_work_increases
-- name    : BitcoinBlockV2.work_increases
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:13:41.374671+00:00
-- url     : https://prove2.me/theorems/9b989ca2-1173-47c2-92f7-b523b90a573a
-- title:
--   Accepted blocks strictly increase the chain work
-- statement:
--   `validate S b now = accept S' undo` implies `S.chainWork < S'.chainWork`: `GetBlockProof` of a header with valid proof of work is at least one, so the most-work rule always prefers an extended chain.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.work_increases (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : BitcoinBlockV2.validate S b now = .accept S' undo) : S.chainWork < S'.chainWork := by sorry
