-- Prove2me | Theorems.Thm_BitcoinSer_serTx_strip
-- name    : BitcoinSer.serTx_strip
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:56:27.340998+00:00
-- url     : https://prove2.me/theorems/19cbe4ff-94c0-4e1d-b392-f5cf113b347f
-- title:
--   The witness-stripped serialization ignores witnesses
-- statement:
--   For every transaction: $\mathrm{serTx}(\mathtt{false}, tx) = \mathrm{serTx}(\mathtt{false}, \mathrm{stripWitness}(tx))$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.serTx_strip (tx : Tx) : BitcoinSer.serTx false tx = BitcoinSer.serTx false tx.stripWitness := by sorry
