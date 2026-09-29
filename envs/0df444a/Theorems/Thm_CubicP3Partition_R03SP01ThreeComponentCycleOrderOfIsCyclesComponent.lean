-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeComponentCycleOrderOfIsCyclesComponent
-- name    : CubicP3Partition.R03SP01ThreeComponentCycleOrderOfIsCyclesComponent
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:08:39.904291+00:00
-- url     : https://prove2.me/theorems/f73f2d97-ba14-4a52-916c-d3ad23bbd03d
-- title:
--   R03 P3-factor structural result: R03SP01ThreeComponentCycleOrderOfIsCyclesComponent
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeComponentCycleOrderOfIsCyclesComponent` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 55dbd330daa2cb37ec42db2cae24ba509a4f569b6bedf9355d62a1f7e19c161d.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-component-zero-one-two-assembly-candidate-v1.lean; source SHA-256 55dbd330daa2cb37ec42db2cae24ba509a4f569b6bedf9355d62a1f7e19c161d; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

open CubicP3Partition
universe u
theorem R03SP01ThreeComponentCycleOrderOfIsCyclesComponent
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
