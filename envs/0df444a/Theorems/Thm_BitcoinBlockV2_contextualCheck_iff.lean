-- Prove2me | Theorems.Thm_BitcoinBlockV2_contextualCheck_iff
-- name    : BitcoinBlockV2.contextualCheck_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:05:32.798303+00:00
-- url     : https://prove2.me/theorems/de7b36f7-10c1-4571-ab1b-1eaca249ed35
-- title:
--   ContextualCheckBlock characterized
-- statement:
--   For a non-empty block whose transactions have inputs, `contextualCheckBlock S b = true` iff `ContextSpec S b`: every transaction final against the lock-time cutoff (median time past once CSV is active, else the block time), the BIP34 coinbase height prefix when active, the witness commitment rule, and the weight limit.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.contextualCheck_iff (S : ChainState) (b : BitcoinSer.Block)
    (hne : b.vtx ≠ []) (hvin : ∀ tx ∈ b.vtx, tx.vin ≠ []) :
    BitcoinBlockV2.contextualCheckBlock S b = true ↔ BitcoinBlockV2.ContextSpec S b := by sorry
