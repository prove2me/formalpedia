-- Prove2me | Theorems.Thm_BitcoinVerify_native_witness_malleated
-- name    : BitcoinVerify.native_witness_malleated
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T15:05:43.986997+00:00
-- url     : https://prove2.me/theorems/e8f1bea6-710a-4cd3-9436-cd7828837463
-- title:
--   A witness-program output needs an empty scriptSig
-- statement:
--   With the `WITNESS` flag, if the output script is a witness program and the scriptSig is non-empty, `verifyScript` is `false` whatever the witness (`SCRIPT_ERR_WITNESS_MALLEATED`).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinVerify
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.native_witness_malleated (tap : TaprootHandler) (c : Ctx) (scriptSig spk : Bytes)
    (w : List Bytes) (hf : c.flags.witness = true) (hw : BitcoinVerify.isWitnessProgram spk ≠ none)
    (hs : scriptSig ≠ []) : BitcoinVerify.verifyScript tap c scriptSig spk w = false := by sorry
