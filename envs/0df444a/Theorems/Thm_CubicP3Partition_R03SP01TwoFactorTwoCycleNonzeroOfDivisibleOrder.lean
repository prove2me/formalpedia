-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder
-- name    : CubicP3Partition.R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T00:44:48.50789+00:00
-- url     : https://prove2.me/theorems/15cc1dad-fc7c-4745-9301-a905f741ae85
-- title:
--   R03 P3-factor structural result: R03 s p01 two factor two cycle nonzero of divisible order
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-two-factor-two-cycle-component-bridge-candidate-v2.lean; source SHA-256 01a64493556ead9bc94d1f9ec67ab66a7a66639ec974154d8116723fcc4ca963; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

open CubicP3Partition
open SimpleGraph
universe u
theorem R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    [Fintype cA.supp] [Fintype cB.supp]
    (horder : 3 ∣ Fintype.card V)
    (hnotzero : ¬(3 ∣ Fintype.card cA.supp ∧ 3 ∣ Fintype.card cB.supp))
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by sorry

end CubicP3Partition
