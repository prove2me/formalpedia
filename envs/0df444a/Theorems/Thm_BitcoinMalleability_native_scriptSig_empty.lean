-- Prove2me | Theorems.Thm_BitcoinMalleability_native_scriptSig_empty
-- name    : BitcoinMalleability.native_scriptSig_empty
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T00:01:29.152327+00:00
-- url     : https://prove2.me/theorems/dec34231-a7b5-4037-926a-e912bc2a01ec
-- title:
--   An input spending a native witness program has an empty scriptSig when its script verifies
-- statement:
--   For script flags with `WITNESS` set, a ledger $u$ and a transaction whose `CheckInputScripts` succeeds: every input whose spent output is a native witness program has `scriptSig = []`. (`VerifyScript` returns `SCRIPT_ERR_WITNESS_MALLEATED` otherwise; the VerifyScript mission's `native_witness_malleated` lifted to the block mission's per-input loop.)
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript (SCRIPT_ERR_WITNESS_MALLEATED, SCRIPT_ERR_WITNESS_MALLEATED_P2SH), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CTransaction::ComputeHash, SerializeTransaction (primitives/transaction.h, transaction.cpp); CheckInputScripts (validation.cpp); BIP141 (Transaction ID)

import Definitions.Def_BitcoinMalleability
import Definitions.Def_BitcoinActivation
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinVerify
open BitcoinMalleability BitcoinSer BitcoinBlockV2

theorem BitcoinMalleability.native_scriptSig_empty (f : BitcoinActivation.ScriptFlags) (u : Ledger)
    (tx : BitcoinSer.Tx) (hf : f.witness = true) (h : BitcoinBlockV2.inputScriptsOk f u tx = true) :
    ∀ i ∈ tx.vin, BitcoinVerify.isWitnessProgram (BitcoinBlockV2.accessCoin u i.prevout).out.scriptPubKey ≠ none →
      i.scriptSig = [] := by sorry
