-- Prove2me | Theorems.Thm_BitcoinSer_compactSize_range
-- name    : BitcoinSer.compactSize_range
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:55:44.685967+00:00
-- url     : https://prove2.me/theorems/82c2ea22-a011-469b-b225-32ef16ca3b64
-- title:
--   A read CompactSize is bounded
-- statement:
--   Every value a successful $\mathrm{readCompactSize}$ returns is below $2^{64}$, and below or equal to $\mathrm{MAX\_SIZE} = 2^{25}$ when the range check is on.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.compactSize_range (rc : Bool) (b : Bytes) (n : Nat) (rest : Bytes)
    (h : BitcoinSer.readCompactSize rc b = some (n, rest)) :
    n < 2 ^ 64 ∧ (rc = true → n ≤ BitcoinSer.MAX_SIZE) := by sorry
