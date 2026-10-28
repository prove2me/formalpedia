-- Prove2me | Theorems.Thm_BitcoinBlockV2_reachable_wellFormed
-- name    : BitcoinBlockV2.reachable_wellFormed
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:12:06.62103+00:00
-- url     : https://prove2.me/theorems/f6eb8d1e-933b-4407-a2ba-498e08533207
-- title:
--   Reachable states are well formed
-- statement:
--   Every state reachable from the genesis has the genesis header first, pairwise distinct ledger keys, and only spendable coins created at heights between 1 and the tip.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2

theorem BitcoinBlockV2.reachable_wellFormed (S : ChainState) (h : BitcoinBlockV2.Reachable S) :
    BitcoinBlockV2.WellFormed S := by sorry
