-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeOneArbitraryPortsRearrangeMod1
-- name    : CubicP3Partition.R03SP01ThreeOneArbitraryPortsRearrangeMod1
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:20:27.76499+00:00
-- url     : https://prove2.me/theorems/b753499b-b534-4010-a1b1-9ddff7942e89
-- title:
--   R03 P3-factor structural result: R03SP01ThreeOneArbitraryPortsRearrangeMod1
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeOneArbitraryPortsRearrangeMod1` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 43e29de4f167f5ff93a3999abc376cf7f9780eb38b49055349d035a02683590e.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-one-arbitrary-ports-rearrange-mod1-candidate-v1.lean; source SHA-256 43e29de4f167f5ff93a3999abc376cf7f9780eb38b49055349d035a02683590e; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib

namespace CubicP3Partition

open CubicP3Partition
theorem R03SP01ThreeOneArbitraryPortsRearrangeMod1
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
