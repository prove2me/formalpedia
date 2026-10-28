-- Prove2me | Theorems.Thm_BitcoinBlockV2_acceptance
-- name    : BitcoinBlockV2.acceptance
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T15:18:03.061384+00:00
-- url     : https://prove2.me/theorems/22717b69-d630-408a-ac72-073a306d7880
-- title:
--   The acceptance theorem: C(S,B,t) accepts iff V(S,B,t)
-- statement:
--   For every chain state $S$ reachable from the genesis, candidate block $B$ and clock reading $t$:
--   $$R(S) \Longrightarrow \big(\exists S'\,u.\ \mathrm{validate}(S,B,t) = \mathrm{accept}(S',u) \iff \mathrm{Valid}(S,B,t)\big).$$
--   The source-linked validation path — `AcceptBlockHeader`, `CheckBlock`, `ContextualCheckBlock`, `ConnectBlock` with the published subsidy, difficulty, median-time, activation, merkle, script and BIP68 transcriptions — accepts exactly when the declarative specification admits the block: the header predicate (a valid compact target met by the hash, the tip as parent, the required difficulty, the median-time floor, the two-hour ceiling, the version floors), the block predicate, the contextual predicate, and the ledger predicate (BIP30 where it applies, every transaction admissible in sequence with the BIP68 specification and every input script verifying, the coinbase bounded by fees plus the specification subsidy).
--
--   **Formalization Note.** The reachability hypothesis is carried as in the goal contract; the equivalence holds for every state. Temporary future-time rejections are a separate outcome (`futureTime_iff`, `futureTime_transient`), and the resulting state is `ApplySpec` (`apply_spec`).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.acceptance (S : ChainState) (b : BitcoinSer.Block) (now : Int) (hR : BitcoinBlockV2.Reachable S) :
    BitcoinBlockV2.accepts S b now ↔ BitcoinBlockV2.Valid S b now := by sorry
