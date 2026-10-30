-- Prove2me | Theorems.Thm_BitcoinScriptV2_checksig_deletes_one
-- name    : BitcoinScriptV2.checksig_deletes_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:19:35.942889+00:00
-- url     : https://prove2.me/theorems/09027e65-dcb2-483e-9dff-a6f7438b22d9
-- title:
--   OP_CHECKSIG checks against the code with its own signature deleted
-- statement:
--   The oracle at an `OP_CHECKSIG(VERIFY)` checks `sig` against `fadSig v scriptCode sig`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.checksig_deletes_one (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s : BitcoinScriptV2.StateV2) (c : BitcoinScript.Byte)
    (hc : c = BitcoinScript.OP_CHECKSIG ∨ c = BitcoinScript.OP_CHECKSIGVERIFY) (sig pk : BitcoinScript.Bytes) :
    (BitcoinScriptV2.oracleAt v o s (.op c)).checkSig sig pk =
      o.checkSig (BitcoinScriptV2.fadSig v s.scriptCode sig) sig pk := by sorry
