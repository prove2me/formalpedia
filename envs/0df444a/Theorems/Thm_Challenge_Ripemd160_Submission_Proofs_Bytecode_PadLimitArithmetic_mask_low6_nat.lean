-- Prove2me | Theorems.Thm_Challenge_Ripemd160_Submission_Proofs_Bytecode_PadLimitArithmetic_mask_low6_nat
-- name    : Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic.mask_low6_nat
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-27T19:41:16.752653+00:00
-- url     : https://prove2.me/theorems/47d07afe-e740-4eed-9643-f2cf2b52f8e8
-- title:
--   Clear the low six bits of a 256-bit natural number
-- statement:
--   Clear the low six bits of a 256-bit natural number.
--
--   Public Apache-2.0 source contributed by Meganpark980320 in verified Yukon submission 0f4090d0-7dc5-4295-857e-4a8cf37f49fb. Source uses Lean 4.31.0; this selected Nat theorem is independently checked in the displayed provider environment. No full-project port or cross-version definition correspondence is claimed.
-- source:
--   https://github.com/Layr-Labs/eip8200-challenges/blob/cdbceb0fd6e3ea82432bb86d83b69601fbb2f37a/Challenge/Ripemd160/Submission/Proofs/Bytecode/PadLimitArithmetic.lean#L7-L30
--
--   yukon-proof-operation:bootstrap-3f89b1a0180a669804a86544210eb921e3cde691031c7b4cc21a62ef5c9f8da6
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Ym9vdHN0cmFwLTNmODliMWEwMTgwYTY2OTgwNGE4NjU0NDIxMGViOTIxZTNjZGU2OTEwMzFjN2I0Y2MyMWE2MmVmNWM5ZjhkYTYiLCJoYXNoIjoiMTdlNTFkMjcxNWEwNzA0ODExMTJiNDdhMjNlYmE2NTIwMmE1OGQ2MDNjNDgzMTNmOTcyOWFlMTBhYzgyYWZiOCIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiQ2hhbGxlbmdlLlJpcGVtZDE2MC5TdWJtaXNzaW9uLlByb29mcy5CeXRlY29kZS5QYWRMaW1pdEFyaXRobWV0aWMubWFza19sb3c2X25hdCIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6ImVpcDgyMDAifQ]

import Mathlib
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic

theorem mask_low6_nat (n : Nat) (hn : n < 2 ^ 256) :
    (2 ^ 256 - 1 - 63) &&& n = n >>> 6 <<< 6 := by sorry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic
