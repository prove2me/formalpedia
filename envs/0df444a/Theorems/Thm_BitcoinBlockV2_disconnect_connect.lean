-- Prove2me | Theorems.Thm_BitcoinBlockV2_disconnect_connect
-- name    : BitcoinBlockV2.disconnect_connect
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:15:33.230687+00:00
-- url     : https://prove2.me/theorems/a507b8b8-e9cd-45fb-9a30-6844e3e887a1
-- title:
--   DisconnectBlock undoes ConnectBlock
-- statement:
--   For a well-formed state, a block with pairwise distinct txids whose outputs do not pre-exist (the BIP30 condition that BIP34 guarantees on mainnet) and that is not the genesis, if `validate S b now = accept S' undo` then `disconnectBlock S'.utxo height hash b undo = some (u, true)` for a ledger $u$ with exactly the coins of `S.utxo`: the undo data restores the previous ledger and the disconnect is clean.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.disconnect_connect (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hwf : BitcoinBlockV2.WellFormed S) (hnd : (b.vtx.map BitcoinSer.txid).Nodup)
    (hfresh : ∀ tx ∈ b.vtx, ∀ o, BitcoinBlockV2.getCoin S.utxo ⟨BitcoinSer.txid tx, o⟩ = none)
    (hg : BitcoinSer.headerHash b.header ≠ BitcoinSer.genesisHash)
    (h : BitcoinBlockV2.validate S b now = .accept S' undo) :
    ∃ u, BitcoinBlockV2.disconnectBlock S'.utxo S.nextHeight (BitcoinSer.headerHash b.header) b undo = some (u, true) ∧
      BitcoinBlockV2.Equiv u S.utxo := by sorry
