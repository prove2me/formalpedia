-- Prove2me | Theorems.Thm_BitcoinSer_serBlock_injective
-- name    : BitcoinSer.serBlock_injective
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:57:46.993362+00:00
-- url     : https://prove2.me/theorems/7d23f02c-d69b-4c0b-a4b4-d5aa7376c98c
-- title:
--   Block serialization is injective
-- statement:
--   For well-formed blocks $b_1, b_2$: $\mathrm{serBlock}(\mathtt{true}, b_1) = \mathrm{serBlock}(\mathtt{true}, b_2) \Rightarrow b_1 = b_2$. Consequently distinct well-formed blocks have distinct byte strings, and a hash of the serialization identifies the block up to hash collisions.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.serBlock_injective (b₁ b₂ : Block) (h₁ : b₁.wf) (h₂ : b₂.wf)
    (h : BitcoinSer.serBlock true b₁ = BitcoinSer.serBlock true b₂) : b₁ = b₂ := by sorry
