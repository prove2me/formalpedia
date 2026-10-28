-- Prove2me | Theorems.Thm_BitcoinSer_genesis_hash
-- name    : BitcoinSer.genesis_hash
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:57:33.926229+00:00
-- url     : https://prove2.me/theorems/b60bfb68-862c-410d-9d4c-e4e44a85866e
-- title:
--   The genesis header hashes to hashGenesisBlock
-- statement:
--   $\mathrm{headerHash}(\mathrm{genesisHeader}) = \mathrm{genesisHash}$: the transcribed genesis header (with the merkle root computed from the coinbase) double-SHA-256's to `000000000019d668…0a8ce26f`, the mainnet genesis hash of `chainparams.cpp`. Checked by kernel evaluation; this ties the hash transcription to the real chain.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.genesis_hash : BitcoinSer.headerHash BitcoinSer.genesisHeader = BitcoinSer.genesisHash := by sorry
