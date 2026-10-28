-- Prove2me | Theorems.Thm_BitcoinSer_block_roundtrip
-- name    : BitcoinSer.block_roundtrip
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:57:55.406935+00:00
-- url     : https://prove2.me/theorems/95eb3ccd-be69-482a-b81f-c45ada5d1980
-- title:
--   Blocks round-trip
-- statement:
--   For every well-formed block $b$, witness mode $aw$ and remainder $r$:
--   $$\mathrm{readBlock}(aw, \mathrm{serBlock}(aw, b) ++ r) = \mathrm{some}\big(\langle b.\mathrm{header},\ b.\mathrm{vtx}\text{ mapped by (if } aw \text{ then id else stripWitness)}\rangle,\ r\big).$$
--   Deserialization is a left inverse of serialization on well-formed blocks in both formats: a block read back from its own bytes is the block (with witnesses, in the witness-aware reader; without, in the legacy one). This is the "interpretation of serialized data" that every hash commitment — merkle root, block hash, txid — refers to.
--
--   **Formalization Note.** Well-formedness is the field-range predicate of the definition (32-bit fields, 32-byte hashes, 64-bit amounts, vector lengths at most $\mathrm{MAX\_SIZE}$, every transaction with an input or a witness); the last condition reflects the dummy-`vin` reinterpretation of the source.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.block_roundtrip (aw : Bool) (b : Block) (rest : Bytes) (hw : b.wf) :
    BitcoinSer.readBlock aw (BitcoinSer.serBlock aw b ++ rest) =
      some (⟨b.header, b.vtx.map (fun tx => if aw then tx else tx.stripWitness)⟩, rest) := by sorry
