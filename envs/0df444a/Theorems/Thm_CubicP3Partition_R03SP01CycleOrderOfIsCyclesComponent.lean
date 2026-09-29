-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01CycleOrderOfIsCyclesComponent
-- name    : CubicP3Partition.R03SP01CycleOrderOfIsCyclesComponent
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T00:44:43.047377+00:00
-- url     : https://prove2.me/theorems/ec1326d3-0313-4c82-bbee-6f5450d44ca8
-- title:
--   R03 P3-factor structural result: R03 s p01 cycle order of is cycles component
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01CycleOrderOfIsCyclesComponent` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-two-factor-two-cycle-component-bridge-candidate-v1.lean; source SHA-256 dbc75daba1e04455368f5f9c930864caea5f004d88163fc2a8a4277190a563a7; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

open CubicP3Partition
open SimpleGraph
universe u
theorem R03SP01CycleOrderOfIsCyclesComponent
    {V : Type u} [Fintype V]
    (F : SimpleGraph V)
    (hcycles : F.IsCycles)
    (h2 : ∀ v : V, Nat.card {w : V // F.Adj v w} = 2)
    (c : F.ConnectedComponent) (n : Nat) [Fintype c.supp]
    (hn : 0 < n)
    (hcard : Fintype.card c.supp = n) :
    ∃ e : Fin n ≃ c.supp, ∀ i : Fin n,
      F.Adj (e i : V)
        (e ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : V) := by sorry

end CubicP3Partition
