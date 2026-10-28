-- Prove2me | Theorems.Thm_BitcoinSer_sha256_length
-- name    : BitcoinSer.sha256_length
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:56:59.624909+00:00
-- url     : https://prove2.me/theorems/795c5465-f427-4874-8112-01413311714d
-- title:
--   SHA-256 outputs 32 bytes
-- statement:
--   For every message: $|\mathrm{sha256}(m)| = 32$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.sha256_length (m : Bytes) : (BitcoinSer.sha256 m).length = 32 := by sorry
