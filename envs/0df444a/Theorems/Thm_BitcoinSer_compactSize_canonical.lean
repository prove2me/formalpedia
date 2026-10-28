-- Prove2me | Theorems.Thm_BitcoinSer_compactSize_canonical
-- name    : BitcoinSer.compactSize_canonical
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:55:19.010986+00:00
-- url     : https://prove2.me/theorems/9e1a884c-a959-40a6-a1cf-29395b56d8a3
-- title:
--   ReadCompactSize accepts only canonical encodings
-- statement:
--   For every mode, byte list $b$, value $n$ and remainder $r$: if $\mathrm{readCompactSize}(b) = \mathrm{some}(n, r)$ then $b = \mathrm{writeCompactSize}(n) ++ r$. The reader is injective on encodings: a value has exactly one accepted encoding, so a CompactSize can never be padded to a longer form.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.compactSize_canonical (rc : Bool) (b : Bytes) (n : Nat) (rest : Bytes)
    (h : BitcoinSer.readCompactSize rc b = some (n, rest)) : b = BitcoinSer.writeCompactSize n ++ rest := by sorry
