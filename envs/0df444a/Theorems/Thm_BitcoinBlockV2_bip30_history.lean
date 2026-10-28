-- Prove2me | Theorems.Thm_BitcoinBlockV2_bip30_history
-- name    : BitcoinBlockV2.bip30_history
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:06:12.020718+00:00
-- url     : https://prove2.me/theorems/cd520a46-be8e-41f9-8195-409bcc13c9a7
-- title:
--   When the BIP30 scan is skipped
-- statement:
--   `bip30Checked S height hash = false` iff $height < 1{,}983{,}702$ and either the block is one of the two `IsBIP30Repeat` blocks or the chain has the BIP34 activation block (height 227,931) with hash `BIP34Hash` as an ancestor. On mainnet the scan is therefore skipped from height 227,932 to 1,983,701 except where BIP34 does not hold, and always performed from 1,983,702.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader

theorem BitcoinBlockV2.bip30_history (S : ChainState) (height : Nat) (hash : BitcoinSer.Bytes) :
    BitcoinBlockV2.bip30Checked S height hash = false ↔
      height < BIP34_IMPLIES_BIP30_LIMIT ∧
      (BitcoinBlockV2.isBIP30Repeat height hash = true ∨
        ∃ h, S.headers[BitcoinHeader.BIP34Height]? = some h ∧ BitcoinSer.headerHash h = BitcoinBlockV2.bip34Hash) := by sorry
