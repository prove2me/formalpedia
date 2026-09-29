-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeOneArbitraryPortsTargetMod1
-- name    : CubicP3Partition.R03SP01ThreeOneArbitraryPortsTargetMod1
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:20:48.108681+00:00
-- url     : https://prove2.me/theorems/e6b81c7a-4cfd-4286-8b0e-5d281cc67b08
-- title:
--   R03 P3-factor structural result: R03SP01ThreeOneArbitraryPortsTargetMod1
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeOneArbitraryPortsTargetMod1` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 895a90cd7e81cd4722f7301faecd8813f5d01a8d4b10d4afa6f895262abeecc4.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-one-arbitrary-ports-target-mod1-candidate-v1.lean; source SHA-256 895a90cd7e81cd4722f7301faecd8813f5d01a8d4b10d4afa6f895262abeecc4; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib

namespace CubicP3Partition

open CubicP3Partition
theorem R03SP01ThreeOneArbitraryPortsTargetMod1
    {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (a b c k1 k2 : Nat)
    (eA : Fin (1 + a * 3) ≃ A)
    (eB : Fin (1 + b * 3) ≃ B)
    (eC : Fin (1 + c * 3) ≃ C)
    (eIndex : Fin (k1 * 3) ⊕ (Fin (k2 * 3) ⊕ Fin 4) ≃
      Fin (1 + b * 3)) :
    Nonempty
      (((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) ≃
        (A ⊕ (B ⊕ C))) := by sorry

end CubicP3Partition
