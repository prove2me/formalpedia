-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01TwoComponentSupportEquiv
-- name    : CubicP3Partition.R03SP01TwoComponentSupportEquiv
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T00:44:45.37506+00:00
-- url     : https://prove2.me/theorems/c47942ce-e8da-4553-9d82-0a441bb3c6b5
-- title:
--   R03 P3-factor structural result: R03 s p01 two component support equiv
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01TwoComponentSupportEquiv` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-two-factor-two-cycle-component-bridge-candidate-v1.lean; source SHA-256 dbc75daba1e04455368f5f9c930864caea5f004d88163fc2a8a4277190a563a7; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

open CubicP3Partition
open SimpleGraph
universe u
theorem R03SP01TwoComponentSupportEquiv
    {V : Type u} [Fintype V]
    (F : SimpleGraph V)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp) :
    ∃ (eV : cA.supp ⊕ cB.supp ≃ V),
      (∀ x : cA.supp, eV (Sum.inl x) = x.1) ∧
      (∀ x : cB.supp, eV (Sum.inr x) = x.1) := by sorry

end CubicP3Partition
