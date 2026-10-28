-- Prove2me | Theorems.Thm_BitcoinBlockV2_validate_clock
-- name    : BitcoinBlockV2.validate_clock
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:02:01.751648+00:00
-- url     : https://prove2.me/theorems/d766da91-e762-4c12-9760-7fdfbc676919
-- title:
--   The clock only matters through the future-time test
-- statement:
--   If `validate S b now ≠ futureTime` and $now \le now'$, then `validate S b now' = validate S b now`: an outcome that is not a time rejection is stable under later clock readings.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.validate_clock (S : ChainState) (b : BitcoinSer.Block) (now now' : Int)
    (h : BitcoinBlockV2.validate S b now ≠ .futureTime) (hle : now ≤ now') :
    BitcoinBlockV2.validate S b now' = BitcoinBlockV2.validate S b now := by sorry
