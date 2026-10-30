-- Prove2me | Theorems.Thm_BitcoinScriptV2_multisigSigs_eq
-- name    : BitcoinScriptV2.multisigSigs_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:20:14.959503+00:00
-- url     : https://prove2.me/theorems/eca3db76-28cb-4f02-967b-a08206d1e38f
-- title:
--   The multisig signatures are read off the stack layout
-- statement:
--   For a stack `nk :: keys ++ ns :: sigs ++ rest` with `nk`, `ns` decoding to the lengths of `keys` and `sigs`: `multisigSigs … = sigs`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.multisigSigs_eq (nk ns : BitcoinScript.Bytes) (keys sigs rest : List BitcoinScript.Bytes)
    (nKeys nSigs : Int) (hk : BitcoinScript.toNum false BitcoinScript.nDefaultMaxNumSize nk = some nKeys)
    (hkl : keys.length = nKeys.toNat) (hn : BitcoinScript.toNum false BitcoinScript.nDefaultMaxNumSize ns = some nSigs)
    (hsl : sigs.length = nSigs.toNat) :
    BitcoinScriptV2.multisigSigs (nk :: (keys ++ ns :: (sigs ++ rest))) = sigs := by sorry
