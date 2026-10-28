-- Prove2me | Theorems.Thm_BitcoinVerify_witness_unexpected
-- name    : BitcoinVerify.witness_unexpected
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T15:05:57.938319+00:00
-- url     : https://prove2.me/theorems/606b50fe-ac9b-4fd1-9b57-859dda9a8fb5
-- title:
--   An unconsumed witness fails
-- statement:
--   With the `WITNESS` flag, if the output is neither a witness program nor P2SH and the witness is non-empty, `verifyScript` is `false` (`SCRIPT_ERR_WITNESS_UNEXPECTED`).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinVerify
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.witness_unexpected (tap : TaprootHandler) (c : Ctx) (scriptSig spk : Bytes) (w : List Bytes)
    (hf : c.flags.witness = true) (hw : BitcoinVerify.isWitnessProgram spk = none)
    (hp : BitcoinVerify.isPayToScriptHash spk = false) (hne : w ≠ []) :
    BitcoinVerify.verifyScript tap c scriptSig spk w = false := by sorry
