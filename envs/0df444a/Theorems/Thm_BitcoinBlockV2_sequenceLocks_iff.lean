-- Prove2me | Theorems.Thm_BitcoinBlockV2_sequenceLocks_iff
-- name    : BitcoinBlockV2.sequenceLocks_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:08:17.422713+00:00
-- url     : https://prove2.me/theorems/a70a4d9f-4a9f-4891-a6f9-2cbbc53213f5
-- title:
--   SequenceLocks is the BIP68 specification
-- statement:
--   `sequenceLocksOk u height mtp ltf tx = true` iff the BIP68 mission's `satisfiesBIP68` holds for the transaction's version, the lock-time flags, the context (height, median times) and the inputs' sequences and coin heights — with no admissibility hypothesis, through the published `fold_acceptance`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.sequenceLocks_iff (u : Ledger) (height : Nat) (mtp : Nat → Nat) (ltf : Nat) (tx : BitcoinSer.Tx) :
    BitcoinBlockV2.sequenceLocksOk u height mtp ltf tx = true ↔
      BitcoinBIP68.satisfiesBIP68 (BitVec.ofNat 32 tx.version) (BitVec.ofNat 32 ltf) ⟨height, mtp⟩
        (tx.vin.map fun i => ⟨BitVec.ofNat 32 i.nSequence, (BitcoinBlockV2.accessCoin u i.prevout).height⟩) := by sorry
