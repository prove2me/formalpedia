-- Prove2me | Theorems.Thm_BitcoinSer_serHeader_length
-- name    : BitcoinSer.serHeader_length
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:55:54.610645+00:00
-- url     : https://prove2.me/theorems/ab0d0c49-5c06-4468-8ae5-53889a677f56
-- title:
--   A block header serializes to 80 bytes
-- statement:
--   For every well-formed header $h$: $|\mathrm{serHeader}(h)| = 80$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.serHeader_length (h : Header) (hw : h.wf) : (BitcoinSer.serHeader h).length = 80 := by sorry
