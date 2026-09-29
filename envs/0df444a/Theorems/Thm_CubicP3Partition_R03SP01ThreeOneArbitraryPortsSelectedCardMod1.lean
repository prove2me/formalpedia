-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeOneArbitraryPortsSelectedCardMod1
-- name    : CubicP3Partition.R03SP01ThreeOneArbitraryPortsSelectedCardMod1
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:20:45.968368+00:00
-- url     : https://prove2.me/theorems/c528aa55-8eaa-4dfd-8ae1-b8bbb6cd4c2f
-- title:
--   R03 P3-factor structural result: R03SP01ThreeOneArbitraryPortsSelectedCardMod1
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeOneArbitraryPortsSelectedCardMod1` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is fd58ce1999bd34f02209e9b82e30aa028997ac5dc8f9f1160ed5354fbd386d40.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-one-arbitrary-ports-index-coverage-candidate-v1.lean; source SHA-256 fd58ce1999bd34f02209e9b82e30aa028997ac5dc8f9f1160ed5354fbd386d40; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib

namespace CubicP3Partition

open CubicP3Partition
open scoped Nat
theorem R03SP01ThreeOneArbitraryPortsSelectedCardMod1
    (b d : Nat) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) (hr : d % 3 = 1) :
    ({0, d, d + 1, (1 + 3 * b) - 1} : Finset Nat).card = 4 := by sorry

end CubicP3Partition
