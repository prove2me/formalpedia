-- Prove2me | Theorems.Thm_BitcoinSer_weight_no_witness
-- name    : BitcoinSer.weight_no_witness
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:56:47.841981+00:00
-- url     : https://prove2.me/theorems/db79ed63-4aef-4b9c-81c7-7586396da594
-- title:
--   Without witnesses the weight is four times the size
-- statement:
--   For every transaction with no witness: the two serializations coincide, and $\mathrm{txWeight}(tx) = 4 \cdot |\mathrm{serTx}(\mathtt{false}, tx)|$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.weight_no_witness (tx : Tx) (h : tx.hasWitness = false) :
    BitcoinSer.serTx true tx = BitcoinSer.serTx false tx ∧
      BitcoinSer.txWeight tx = BitcoinSer.WITNESS_SCALE_FACTOR * (BitcoinSer.serTx false tx).length := by sorry
