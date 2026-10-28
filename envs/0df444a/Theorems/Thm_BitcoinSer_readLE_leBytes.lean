-- Prove2me | Theorems.Thm_BitcoinSer_readLE_leBytes
-- name    : BitcoinSer.readLE_leBytes
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:54:47.204041+00:00
-- url     : https://prove2.me/theorems/b56ed122-ef2a-4c00-a24a-aa9d6ebedd61
-- title:
--   Fixed-width integers round-trip
-- statement:
--   For all $k$, $n < 2^{8k}$ and remainder $r$: $\mathrm{readLE}(k, \mathrm{leBytes}(k,n) ++ r) = \mathrm{some}(n, r)$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.readLE_leBytes (k n : Nat) (rest : Bytes) (h : n < 2 ^ (8 * k)) :
    BitcoinSer.readLE k (BitcoinSer.leBytes k n ++ rest) = some (n, rest) := by sorry
