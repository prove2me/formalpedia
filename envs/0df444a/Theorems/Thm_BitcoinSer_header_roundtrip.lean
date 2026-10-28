-- Prove2me | Theorems.Thm_BitcoinSer_header_roundtrip
-- name    : BitcoinSer.header_roundtrip
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:56:04.975975+00:00
-- url     : https://prove2.me/theorems/3d0b669a-96e9-4e6f-aed0-49506e485746
-- title:
--   Block headers round-trip
-- statement:
--   For every well-formed header $h$ and remainder $r$: $\mathrm{readHeader}(\mathrm{serHeader}(h) ++ r) = \mathrm{some}(h, r)$, including the signed `nVersion`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.header_roundtrip (h : Header) (rest : Bytes) (hw : h.wf) :
    BitcoinSer.readHeader (BitcoinSer.serHeader h ++ rest) = some (h, rest) := by sorry
