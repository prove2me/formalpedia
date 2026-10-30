-- Prove2me | Theorems.Thm_BitcoinScriptV2_annotate_parse
-- name    : BitcoinScriptV2.annotate_parse
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:18:22.571149+00:00
-- url     : https://prove2.me/theorems/404f3dfd-17d1-4c82-a5f1-46ebba21faf7
-- title:
--   The annotated parse projects to the published parse
-- statement:
--   `(annotate s).map (List.map Prod.fst) = parseScript s`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.annotate_parse (s : BitcoinScript.Bytes) :
    (BitcoinScriptV2.annotate s).map (List.map Prod.fst) = BitcoinSig.parseScript s := by sorry
