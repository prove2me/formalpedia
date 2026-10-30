-- Prove2me | Theorems.Thm_BitcoinScriptV2_multisig_deletes_all
-- name    : BitcoinScriptV2.multisig_deletes_all
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:20:25.109383+00:00
-- url     : https://prove2.me/theorems/595b4a9d-a121-4a57-aa48-c023a0d3f773
-- title:
--   OP_CHECKMULTISIG checks every signature against the code with all its signatures deleted (L10 closed)
-- statement:
--   The oracle at an `OP_CHECKMULTISIG(VERIFY)` checks each `sig` against `fadAll v scriptCode (multisigSigs stack)`: Core deletes all `nSigsCount` signature pushes before any check.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.multisig_deletes_all (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s : BitcoinScriptV2.StateV2) (c : BitcoinScript.Byte)
    (hc : c = BitcoinScript.OP_CHECKMULTISIG ∨ c = BitcoinScript.OP_CHECKMULTISIGVERIFY) (sig pk : BitcoinScript.Bytes) :
    (BitcoinScriptV2.oracleAt v o s (.op c)).checkSig sig pk =
      o.checkSig (BitcoinScriptV2.fadAll v s.scriptCode (BitcoinScriptV2.multisigSigs s.st.stack)) sig pk := by sorry
