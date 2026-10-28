-- Prove2me | Theorems.Thm_BitcoinVerify_isWitnessProgram_iff
-- name    : BitcoinVerify.isWitnessProgram_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T15:05:11.60627+00:00
-- url     : https://prove2.me/theorems/43212ceb-6646-4259-9f97-3a335ba3cc32
-- title:
--   IsWitnessProgram characterized
-- statement:
--   `isWitnessProgram s = some (v, program)` iff $v \le 16$, $2 \le |program| \le 40$ and $s$ is `OP_v <program>` (a single direct push), i.e. `witnessBytes v program`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinVerify
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.isWitnessProgram_iff (s : Bytes) (v : Nat) (prog : Bytes) :
    BitcoinVerify.isWitnessProgram s = some (v, prog) ↔
      v ≤ 16 ∧ 2 ≤ prog.length ∧ prog.length ≤ 40 ∧ s = BitcoinVerify.witnessBytes v prog := by sorry
