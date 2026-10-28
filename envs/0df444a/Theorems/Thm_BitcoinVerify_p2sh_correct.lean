-- Prove2me | Theorems.Thm_BitcoinVerify_p2sh_correct
-- name    : BitcoinVerify.p2sh_correct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T15:06:28.965476+00:00
-- url     : https://prove2.me/theorems/e55f5935-1cd6-4da6-b4cb-bb94b01c206f
-- title:
--   P2SH is correct
-- statement:
--   With the `P2SH` flag, the output `OP_HASH160 <h> OP_EQUAL` spent with the push-only scriptSig $\langle a_1\rangle \cdots \langle a_k\rangle \langle redeem\rangle$ and no witness, where $redeem$ is not a witness program, verifies iff $\mathrm{Hash160}(redeem) = h$ and $redeem$, run on the stack $[a_k, \dots, a_1]$, leaves a true top. The side conditions are the push and stack limits (elements within 520 bytes, at most 1000 elements, scriptSig within 10,000 bytes).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.p2sh_correct (tap : TaprootHandler) (c : Ctx) (args : List Bytes) (redeem h : Bytes)
    (hp : c.flags.p2sh = true) (hh : h.length = 20)
    (hargs : ∀ a ∈ args, a.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hred : redeem.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hn : args.length + 2 ≤ BitcoinScript.MAX_STACK_SIZE)
    (hsz : (BitcoinVerify.pushesBytes (args ++ [redeem])).length ≤ BitcoinVerify.MAX_SCRIPT_SIZE)
    (hnw : BitcoinVerify.isWitnessProgram redeem = none) :
    BitcoinVerify.verifyScript tap c (BitcoinVerify.pushesBytes (args ++ [redeem])) (BitcoinVerify.p2shBytes h) [] = true ↔
      BitcoinSer.hash160 redeem = h ∧
      ∃ st, BitcoinVerify.evalBytes c .base args.reverse redeem = some st ∧ BitcoinVerify.topTrue st = true := by sorry
