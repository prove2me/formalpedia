-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01TwoCycleCyclicOrderAssemblyAtCross
-- name    : CubicP3Partition.R03SP01TwoCycleCyclicOrderAssemblyAtCross
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T00:44:33.264106+00:00
-- url     : https://prove2.me/theorems/03813fcb-9d52-4b9e-be39-b4a09f97b906
-- title:
--   R03 P3-factor structural result: R03 s p01 two cycle cyclic order assembly at cross
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01TwoCycleCyclicOrderAssemblyAtCross` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-two-cycle-cyclic-order-assembly-candidate-v4.lean; source SHA-256 3e71ed2bb9ce6b00448449d6c9fc5c8803ecfcddbd386a00613e6a0710412cdd; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

open CubicP3Partition
open SimpleGraph
universe u
theorem R03SP01TwoCycleCyclicOrderAssemblyAtCross
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (1 + kA * 3) ≃ A)
    (eB : Fin (2 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (2 + kB * 3),
      G.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (iA : Fin (1 + kA * 3)) (iB : Fin (2 + kB * 3))
    (cross : G.Adj (Sum.inl (eA iA)) (Sum.inr (eB iB))) :
    Nonempty (P3Factor G) := by sorry

end CubicP3Partition
