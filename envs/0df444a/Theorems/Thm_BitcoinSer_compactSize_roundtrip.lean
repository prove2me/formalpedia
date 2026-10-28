-- Prove2me | Theorems.Thm_BitcoinSer_compactSize_roundtrip
-- name    : BitcoinSer.compactSize_roundtrip
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:55:00.824076+00:00
-- url     : https://prove2.me/theorems/dc93f7a7-0076-4028-b933-bbeb1a153e70
-- title:
--   CompactSize round-trips
-- statement:
--   For all $n < 2^{64}$ and $r$: $\mathrm{readCompactSize}(\mathtt{false}, \mathrm{writeCompactSize}(n) ++ r) = \mathrm{some}(n, r)$ — the unchecked reader accepts every encoding the writer produces, in all four width classes.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.compactSize_roundtrip (n : Nat) (rest : Bytes) (h : n < 2 ^ 64) :
    BitcoinSer.readCompactSize false (BitcoinSer.writeCompactSize n ++ rest) = some (n, rest) := by sorry
