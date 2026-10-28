-- Prove2me | Theorems.Thm_BitcoinSer_hash160_length
-- name    : BitcoinSer.hash160_length
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:57:09.862993+00:00
-- url     : https://prove2.me/theorems/13774613-2ca2-4bd6-9859-8455e12e8e24
-- title:
--   Hash160 outputs 20 bytes
-- statement:
--   For every message: $|\mathrm{hash160}(m)| = 20$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.hash160_length (m : Bytes) : (BitcoinSer.hash160 m).length = 20 := by sorry
