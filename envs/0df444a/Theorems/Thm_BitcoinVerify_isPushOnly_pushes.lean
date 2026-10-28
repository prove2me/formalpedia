-- Prove2me | Theorems.Thm_BitcoinVerify_isPushOnly_pushes
-- name    : BitcoinVerify.isPushOnly_pushes
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T15:05:32.020999+00:00
-- url     : https://prove2.me/theorems/af94ffc0-cd54-47fb-b4c8-9e50aa334535
-- title:
--   A push-only scriptSig satisfies IsPushOnly
-- statement:
--   For elements each within 520 bytes, `isPushOnly (pushesBytes ps) = true`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.isPushOnly_pushes (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.isPushOnly (BitcoinVerify.pushesBytes ps) = true := by sorry
