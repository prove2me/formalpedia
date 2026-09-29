-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeOneArbitraryPortsArithmetic
-- name    : CubicP3Partition.R03SP01ThreeOneArbitraryPortsArithmetic
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T00:44:23.965776+00:00
-- url     : https://prove2.me/theorems/6a822070-a8fe-4cd9-9e23-64d75cc57288
-- title:
--   R03 P3-factor structural result: R03 s p01 three one arbitrary ports arithmetic
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeOneArbitraryPortsArithmetic` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-one-arbitrary-ports-arithmetic-candidate-v1.lean; source SHA-256 5b04c4667accfd39b7f3278c1f95b4532f7c3a8b2084476596a8a8aeb20171a3; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib

namespace CubicP3Partition

open CubicP3Partition
theorem R03SP01ThreeOneArbitraryPortsArithmetic
    (b d : Nat) (hb : 1 ≤ b) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) :
    (d % 3 = 0 ∧ 3 ∣ d - 3 ∧ 3 ∣ (1 + 3 * b) - d - 1) ∨
    (d % 3 = 1 ∧ 3 ∣ d - 1 ∧ 3 ∣ (1 + 3 * b) - d - 3) ∨
    (d % 3 = 2 ∧ 3 ∣ d - 2 ∧ 3 ∣ (1 + 3 * b) - d - 2) := by sorry

end CubicP3Partition
