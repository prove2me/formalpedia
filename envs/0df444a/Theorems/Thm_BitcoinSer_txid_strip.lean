-- Prove2me | Theorems.Thm_BitcoinSer_txid_strip
-- name    : BitcoinSer.txid_strip
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:56:38.819392+00:00
-- url     : https://prove2.me/theorems/fff9e738-b7fe-4396-8395-ce0424b07756
-- title:
--   The txid does not depend on witness data
-- statement:
--   For every transaction: $\mathrm{txid}(tx) = \mathrm{txid}(\mathrm{stripWitness}(tx))$ — the segregated-witness property that signatures can change without changing the transaction id.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.txid_strip (tx : Tx) : BitcoinSer.txid tx = BitcoinSer.txid tx.stripWitness := by sorry
