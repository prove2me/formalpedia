-- Prove2me | Theorems.Thm_BitcoinScriptV2_legacyOracle_eq
-- name    : BitcoinScriptV2.legacyOracle_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:18:07.377397+00:00
-- url     : https://prove2.me/theorems/57577a34-c418-46db-a6b2-0a26fac0f631
-- title:
--   The published oracle is the V2 oracle with the code fixed
-- statement:
--   `legacyOracle f tx nIn amount v sc = withCodeSig (legacyOracleV2 f tx nIn amount v) v sc`, by definition.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.legacyOracle_eq (f : BitcoinSig.SigFlags) (tx : BitcoinSer.Tx) (nIn : Nat) (amount : Int)
    (v : BitcoinSig.SigVersion) (sc : BitcoinScript.Bytes) :
    BitcoinSig.legacyOracle f tx nIn amount v sc =
      BitcoinScriptV2.withCodeSig (BitcoinScriptV2.legacyOracleV2 f tx nIn amount v) v sc := by sorry
