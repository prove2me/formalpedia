-- Prove2me | Theorems.Thm_BitcoinMalleability_txid_of_intent
-- name    : BitcoinMalleability.txid_of_intent
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T00:02:06.885707+00:00
-- url     : https://prove2.me/theorems/07ec0249-1fdb-4147-96f0-9115ea8dec0c
-- title:
--   For native-SegWit spends the txid is the txid of the intent's canonical transaction
-- statement:
--   For flags with `WITNESS`, a ledger $u$, and a transaction whose scripts verify and whose inputs all spend native witness programs: `txid tx = txid (ofIntent (intentOf tx))`. The txid hashes the witness-stripped serialization; with every `scriptSig` forced empty, nothing chosen by a signer or a third party remains in the hashed bytes.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript (SCRIPT_ERR_WITNESS_MALLEATED, SCRIPT_ERR_WITNESS_MALLEATED_P2SH), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CTransaction::ComputeHash, SerializeTransaction (primitives/transaction.h, transaction.cpp); CheckInputScripts (validation.cpp); BIP141 (Transaction ID)

import Definitions.Def_BitcoinMalleability
import Definitions.Def_BitcoinActivation
import Definitions.Def_BitcoinSer
open BitcoinMalleability BitcoinSer BitcoinBlockV2

theorem BitcoinMalleability.txid_of_intent (f : BitcoinActivation.ScriptFlags) (u : Ledger) (tx : BitcoinSer.Tx)
    (hf : f.witness = true) (h : BitcoinBlockV2.inputScriptsOk f u tx = true)
    (hw : BitcoinMalleability.SpendsWitnessPrograms u tx) :
    BitcoinSer.txid tx = BitcoinSer.txid (BitcoinMalleability.ofIntent (BitcoinMalleability.intentOf tx)) := by sorry
