-- Prove2me | Theorems.Thm_BitcoinBlockV2_connectBlock_iff
-- name    : BitcoinBlockV2.connectBlock_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:09:42.495904+00:00
-- url     : https://prove2.me/theorems/3774e069-3703-4663-ad9e-ce9bcf2d9b35
-- title:
--   ConnectBlock characterized
-- statement:
--   For a non-empty block with non-negative outputs, `connectBlock S b` succeeds iff `LedgerSpec S b`: the genesis shortcut, or the BIP30 freshness where the scan applies, the transaction sequence, and the coinbase value at most the fees plus the specification subsidy (`core_eq_spec`).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.connectBlock_iff (S : ChainState) (b : BitcoinSer.Block) (hne : b.vtx ≠ [])
    (hpos : ∀ tx ∈ b.vtx, 0 ≤ BitcoinBlockV2.valueOut tx) :
    (∃ r, BitcoinBlockV2.connectBlock S b = some r) ↔ BitcoinBlockV2.LedgerSpec S b := by sorry
