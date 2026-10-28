-- Prove2me | Theorems.Thm_BitcoinVerify_unknown_witness_version
-- name    : BitcoinVerify.unknown_witness_version
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T15:06:09.859445+00:00
-- url     : https://prove2.me/theorems/1ea1a6be-c991-46b6-ad47-b4f8b85d772b
-- title:
--   Unknown witness versions are accepted
-- statement:
--   With the `WITNESS` flag, an output `OP_v <program>` with $2 \le v \le 16$, or $v = 1$ with a program that is not 32 bytes (including pay-to-anchor), spent with an empty scriptSig and any witness, verifies exactly when the program is true as a script value. This is the future-soft-fork compatibility rule: such outputs are anyone-can-spend, except that an all-zero program fails the base evaluation.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.unknown_witness_version (tap : TaprootHandler) (c : Ctx) (v : Nat) (prog : Bytes)
    (w : List Bytes) (hf : c.flags.witness = true) (hv : v ≤ 16)
    (hu : 2 ≤ v ∨ (v = 1 ∧ prog.length ≠ 32)) (h2 : 2 ≤ prog.length) (h40 : prog.length ≤ 40) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes v prog) w = BitcoinScript.castToBool prog := by sorry
