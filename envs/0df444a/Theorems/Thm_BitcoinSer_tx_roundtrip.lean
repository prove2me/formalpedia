-- Prove2me | Theorems.Thm_BitcoinSer_tx_roundtrip
-- name    : BitcoinSer.tx_roundtrip
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T13:56:16.90634+00:00
-- url     : https://prove2.me/theorems/02163a4a-d5f7-4b12-b97c-e0b4db08f060
-- title:
--   Transactions round-trip in both formats
-- statement:
--   For every well-formed transaction $tx$, witness mode $aw$ with ($aw$ ⇒ `vin` non-empty), and remainder $r$:
--   $$\mathrm{readTx}(aw, \mathrm{serTx}(aw, tx) ++ r) = \mathrm{some}(\text{if } aw \text{ then } tx \text{ else } \mathrm{stripWitness}(tx),\ r).$$
--   With witnesses allowed the extended format (dummy, flag byte, witness stacks) is parsed back exactly; without, the basic format returns the transaction with cleared witnesses. The non-empty-`vin` side condition is genuine: `UnserializeTransaction` reads an empty `vin` as the BIP144 dummy, so a witness-less, input-less transaction does not round-trip through the witness-aware reader.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp

import Definitions.Def_BitcoinSer

theorem BitcoinSer.tx_roundtrip (aw : Bool) (tx : Tx) (rest : Bytes) (hw : tx.wf)
    (hv : aw = true → tx.vin ≠ []) :
    BitcoinSer.readTx aw (BitcoinSer.serTx aw tx ++ rest) =
      some (if aw then tx else tx.stripWitness, rest) := by sorry
