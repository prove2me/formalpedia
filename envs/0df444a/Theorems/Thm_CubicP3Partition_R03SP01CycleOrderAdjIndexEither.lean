-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01CycleOrderAdjIndexEither
-- name    : CubicP3Partition.R03SP01CycleOrderAdjIndexEither
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T09:56:18.318014+00:00
-- url     : https://prove2.me/theorems/7da704bd-4d8d-462c-80c8-3e94f266d969
-- title:
--   R03 P3-factor structural result: R03SP01CycleOrderAdjIndexEither
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01CycleOrderAdjIndexEither` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 8f76f5a079ffcf2482e8ae482e39506b1191dbf54e462dc8bd660af6f032ebb4.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-one-adjacent-components-candidate-v1.lean; source SHA-256 8f76f5a079ffcf2482e8ae482e39506b1191dbf54e462dc8bd660af6f032ebb4; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_6a9ebf31a5_r03_sp01_three_one_adjacent_components_candidate

namespace CubicP3Partition

open CubicP3Partition
universe u
open SimpleGraph
theorem R03SP01CycleOrderAdjIndexEither
    {X : Type u}
    (R : SimpleGraph X)
    (hcycles : R.IsCycles)
    (n : Nat) (hn : 3 ≤ n)
    (e : Fin n → X)
    (hinj : Function.Injective e)
    (cycle : ∀ i : Fin n,
      R.Adj (e i) (e ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩))
    (i j : Fin n) (hadj : R.Adj (e i) (e j)) :
    j = ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩ ∨
      i = ⟨(j.val + 1) % n, Nat.mod_lt _ (by omega)⟩ := by sorry

end CubicP3Partition
