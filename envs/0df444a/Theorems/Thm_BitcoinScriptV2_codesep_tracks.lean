-- Prove2me | Theorems.Thm_BitcoinScriptV2_codesep_tracks
-- name    : BitcoinScriptV2.codesep_tracks
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:19:24.354678+00:00
-- url     : https://prove2.me/theorems/5cdadee6-4bbe-4af2-b486-55a1a5af4eaa
-- title:
--   The script code after an executed OP_CODESEPARATOR at byte p is the script from p+1 (L1 closed)
-- statement:
--   For an annotated script and its $k$-th instruction `(.op OP_CODESEPARATOR, r)`, an executing successful step gives `scriptCode = r` with `r = script.drop (p+1)` for the opcode's byte position $p$: Core's `pbegincodehash = pc`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.codesep_tracks (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (script : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (hl : BitcoinScriptV2.annotate script = some l) (k : Nat) (r : BitcoinScript.Bytes)
    (hk : l[k]? = some (.op BitcoinScript.OP_CODESEPARATOR, r))
    (s s' : BitcoinScriptV2.StateV2) (hexec : BitcoinScript.allTrue s.st.vfExec = true)
    (h : BitcoinScriptV2.stepV2 f v o s (.op BitcoinScript.OP_CODESEPARATOR, r) = some s') :
    s'.scriptCode = r ∧ ∃ p, script[p]? = some BitcoinScript.OP_CODESEPARATOR ∧ r = script.drop (p + 1) := by sorry
