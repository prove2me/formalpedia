-- Prove2me | Theorems.Thm_BitcoinVerify_p2wsh_correct
-- name    : BitcoinVerify.p2wsh_correct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T15:06:19.349772+00:00
-- url     : https://prove2.me/theorems/8bb1b7f5-a95b-435f-abaf-64a3111b340f
-- title:
--   Native P2WSH characterized
-- statement:
--   With the `WITNESS` flag, the output `OP_0 <SHA256(script)>` spent with an empty scriptSig and witness `ws ++ [script]` verifies iff the program is true as a script value and the witness script, run under witness v0 on the stack of the remaining elements (last on top), leaves exactly one true element.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.p2wsh_correct (tap : TaprootHandler) (c : Ctx) (ws : List Bytes) (script : Bytes)
    (hf : c.flags.witness = true) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 script)) (ws ++ [script]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 script) = true ∧
      BitcoinVerify.executeWitnessScriptV0 c ws.reverse script = true := by sorry
