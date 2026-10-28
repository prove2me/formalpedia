-- Prove2me | Theorems.Thm_BitcoinSer_leBytes_length
-- name    : BitcoinSer.leBytes_length
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:54:35.98705+00:00
-- url     : https://prove2.me/theorems/dcb30940-507f-44ea-a84d-16bf994fe49d
-- title:
--   A fixed-width encoding has its width
-- statement:
--   For all $k, n$: $|\mathrm{leBytes}(k, n)| = k$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.leBytes_length (k n : Nat) : (BitcoinSer.leBytes k n).length = k := by sorry
