-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeOneArbitraryPortsRearrangeMod0
-- name    : CubicP3Partition.R03SP01ThreeOneArbitraryPortsRearrangeMod0
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:20:20.177933+00:00
-- url     : https://prove2.me/theorems/9066fa4c-0cc7-401a-9baf-22e8dbe39533
-- title:
--   R03 P3-factor structural result: R03SP01ThreeOneArbitraryPortsRearrangeMod0
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeOneArbitraryPortsRearrangeMod0` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 13a132628beedcca9a56ff522bbc6096037f4cdc44daa1d4d7caaa0fad75058e.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-one-arbitrary-ports-rearrange-mod0-candidate-v1.lean; source SHA-256 13a132628beedcca9a56ff522bbc6096037f4cdc44daa1d4d7caaa0fad75058e; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib

namespace CubicP3Partition

open CubicP3Partition
theorem R03SP01ThreeOneArbitraryPortsRearrangeMod0
    (a k1 k2 c : Nat) :
    Nonempty
      (((Fin a × Fin 3) ⊕
        ((Fin k1 × Fin 3) ⊕
          ((Fin k2 × Fin 3) ⊕
            ((Fin c × Fin 3) ⊕ (Fin 2 × Fin 3))))) ≃
        (((Fin a × Fin 3) ⊕ Fin 1) ⊕
          ((Fin k1 × Fin 3) ⊕
            ((Fin k2 × Fin 3) ⊕
              (Fin 4 ⊕ ((Fin c × Fin 3) ⊕ Fin 1)))))) := by sorry

end CubicP3Partition
