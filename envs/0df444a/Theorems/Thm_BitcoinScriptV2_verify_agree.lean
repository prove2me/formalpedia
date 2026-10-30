-- Prove2me | Theorems.Thm_BitcoinScriptV2_verify_agree
-- name    : BitcoinScriptV2.verify_agree
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:21:51.900947+00:00
-- url     : https://prove2.me/theorems/ce979ee7-ecb8-4d34-bbdc-05763b8afc69
-- title:
--   Outside the two limits VerifyScript is unchanged: the published verifier is exact there
-- statement:
--   If the scriptSig, the scriptPubKey on the resulting stack, the P2SH redeem script and the witness script are each `EvalOk` in their context: `verifyScriptV2 tap c scriptSig scriptPubKey witness = verifyScript tap c scriptSig scriptPubKey witness`. Hence the published `verifyScript` (and every theorem proved about it) is exact for every script execution that does not execute an `OP_CODESEPARATOR` in a signature-checked legacy script and does not push a multisig's own signature into its script code; `verifyScriptV2` is the exact rule everywhere, as 994 of 994 Core vectors confirm.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.verify_agree (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (scriptSig scriptPubKey : BitcoinScript.Bytes) (witness : List BitcoinScript.Bytes)
    (h1 : BitcoinScriptV2.EvalOk c .base [] scriptSig)
    (h2 : ∀ st, BitcoinScriptV2.evalBytesV2 c .base [] scriptSig = some st → BitcoinScriptV2.EvalOk c .base st scriptPubKey)
    (h3 : ∀ redeem rest, BitcoinScriptV2.evalBytesV2 c .base [] scriptSig = some (redeem :: rest) →
      BitcoinScriptV2.EvalOk c .base rest redeem)
    (h4 : ∀ script, witness.getLast? = some script → BitcoinScriptV2.EvalOk c .witnessV0 witness.dropLast.reverse script) :
    BitcoinScriptV2.verifyScriptV2 tap c scriptSig scriptPubKey witness =
      BitcoinVerify.verifyScript tap c scriptSig scriptPubKey witness := by sorry
