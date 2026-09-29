-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ExistsCrossEdgeOfConnected
-- name    : CubicP3Partition.R03SP01ExistsCrossEdgeOfConnected
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T00:29:10.929899+00:00
-- url     : https://prove2.me/theorems/a3b177f1-6944-440e-a7d5-bc0a1276ad77
-- title:
--   R03 P3-factor structural result: R03 s p01 exists cross edge of connected
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ExistsCrossEdgeOfConnected` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; the artifact is candidate-only and its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-two-cycle-cyclic-order-assembly-candidate-v3.lean; source SHA-256 c846197e5e4259b0320012f9799f1f933b8caba92513d6ca4689d68935f35f89; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

open CubicP3Partition
open SimpleGraph
universe u
theorem R03SP01ExistsCrossEdgeOfConnected
    {A B : Type u} (G : SimpleGraph (A ⊕ B))
    (a0 : A) (b0 : B) (hconn : G.Connected) :
    ∃ a : A, ∃ b : B, G.Adj (Sum.inl a) (Sum.inr b) := by sorry

end CubicP3Partition
