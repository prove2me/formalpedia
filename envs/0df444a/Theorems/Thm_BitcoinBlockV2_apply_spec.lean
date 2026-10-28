-- Prove2me | Theorems.Thm_BitcoinBlockV2_apply_spec
-- name    : BitcoinBlockV2.apply_spec
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:11:31.691977+00:00
-- url     : https://prove2.me/theorems/16b3b708-775f-4e9f-83bb-75f0b06a8bbf
-- title:
--   Apply-spec equality
-- statement:
--   $C(S,B,t) = \mathrm{Accept}(S') \Longrightarrow S' = \mathrm{ApplySpec}(S,B)$: whenever the validation accepts, the resulting state is the declaratively specified one — the headers extended by the block's header and the ledger transformed by the block's transactions in order.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.apply_spec (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : BitcoinBlockV2.validate S b now = .accept S' undo) : S' = BitcoinBlockV2.applySpec S b := by sorry
