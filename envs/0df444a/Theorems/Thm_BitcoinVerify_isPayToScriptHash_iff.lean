-- Prove2me | Theorems.Thm_BitcoinVerify_isPayToScriptHash_iff
-- name    : BitcoinVerify.isPayToScriptHash_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T15:04:58.569399+00:00
-- url     : https://prove2.me/theorems/5d94ad76-070f-4acf-b8bd-5c9e4ab544fa
-- title:
--   IsPayToScriptHash characterized
-- statement:
--   A byte string satisfies `IsPayToScriptHash` iff it is `OP_HASH160 <h> OP_EQUAL` for some 20-byte $h$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinVerify
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.isPayToScriptHash_iff (s : Bytes) :
    BitcoinVerify.isPayToScriptHash s = true ↔ ∃ h : Bytes, h.length = 20 ∧ s = BitcoinVerify.p2shBytes h := by sorry
