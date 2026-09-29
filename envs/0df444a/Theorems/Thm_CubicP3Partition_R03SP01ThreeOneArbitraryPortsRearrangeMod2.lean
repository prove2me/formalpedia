-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeOneArbitraryPortsRearrangeMod2
-- name    : CubicP3Partition.R03SP01ThreeOneArbitraryPortsRearrangeMod2
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:20:33.008671+00:00
-- url     : https://prove2.me/theorems/1cb96864-2ebf-4900-a80f-a8fbe87e5423
-- title:
--   R03 P3-factor structural result: R03SP01ThreeOneArbitraryPortsRearrangeMod2
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeOneArbitraryPortsRearrangeMod2` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is df41f5a2bb0c4c10eea24bf9c63cf73b3a9820b0fc112b69503306960d77f56e.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-one-arbitrary-ports-rearrange-mod2-candidate-v1.lean; source SHA-256 df41f5a2bb0c4c10eea24bf9c63cf73b3a9820b0fc112b69503306960d77f56e; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib

namespace CubicP3Partition

open CubicP3Partition
theorem R03SP01ThreeOneArbitraryPortsRearrangeMod2
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
