-- Prove2me | Theorems.Thm_BitcoinSer_genesis_merkle
-- name    : BitcoinSer.genesis_merkle
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:57:21.002+00:00
-- url     : https://prove2.me/theorems/5fb5f57b-37aa-46e5-b5af-fb3caf3579fd
-- title:
--   The genesis coinbase hashes to the recorded merkle root
-- statement:
--   $\mathrm{txid}(\mathrm{genesisCoinbase}) = \mathrm{genesisMerkleRoot}$: the transcribed genesis coinbase transaction, serialized and double-SHA-256'd by the transcribed algorithms, gives exactly `4a5e1e4b…eda33b`. Checked by kernel evaluation of the full SHA-256.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.genesis_merkle : BitcoinSer.txid BitcoinSer.genesisCoinbase = BitcoinSer.genesisMerkleRoot := by sorry
