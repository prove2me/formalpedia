-- Prove2me | Theorems.Thm_BitcoinBlockV2_connectLoop_iff
-- name    : BitcoinBlockV2.connectLoop_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:09:13.404198+00:00
-- url     : https://prove2.me/theorems/2579761f-2d38-4255-b00f-650a49949297
-- title:
--   The ConnectBlock transaction loop characterized
-- statement:
--   For transactions with non-negative outputs and a non-negative fee total, the loop succeeds iff `TxsSpec`: each non-coinbase is admissible (`TxInputsSpec`) against the ledger left by its predecessors with the fee total within `MAX_MONEY`, and the accumulated sigop cost stays within 80,000, in order.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinActivation
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.connectLoop_iff (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat)
    (txs : List BitcoinSer.Tx) (u : Ledger) (fees : Int) (sigOps : Nat) (undo : BlockUndo)
    (hpos : ∀ tx ∈ txs, 0 ≤ BitcoinBlockV2.valueOut tx) (hfees : 0 ≤ fees) :
    (∃ st, BitcoinBlockV2.connectLoop f H mtp ltf ⟨u, fees, sigOps, undo⟩ txs = some st) ↔
      BitcoinBlockV2.TxsSpec f H mtp ltf u fees sigOps txs := by sorry
