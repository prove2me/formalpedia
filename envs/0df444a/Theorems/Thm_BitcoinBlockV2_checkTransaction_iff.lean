-- Prove2me | Theorems.Thm_BitcoinBlockV2_checkTransaction_iff
-- name    : BitcoinBlockV2.checkTransaction_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:03:52.264893+00:00
-- url     : https://prove2.me/theorems/d3676572-f69f-4024-a8d0-1e3f67a383bd
-- title:
--   CheckTransaction characterized
-- statement:
--   `checkTransaction tx = true` iff `TxSpec tx`: non-empty inputs and outputs, stripped size within the limit, every output value in $[0, \mathrm{MAX\_MONEY}]$ and the total at most `MAX_MONEY`, distinct prevouts, the coinbase script-length rule, and no null prevout for a non-coinbase.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.checkTransaction_iff (tx : BitcoinSer.Tx) :
    BitcoinBlockV2.checkTransaction tx = true ↔ BitcoinBlockV2.TxSpec tx := by sorry
