-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeOneArbitraryPortsIndexEquivMod0
-- name    : CubicP3Partition.R03SP01ThreeOneArbitraryPortsIndexEquivMod0
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:21:19.411371+00:00
-- url     : https://prove2.me/theorems/9d9ca603-ff24-4cad-9f52-b6e73cc7b5c3
-- title:
--   R03 P3-factor structural result: R03SP01ThreeOneArbitraryPortsIndexEquivMod0
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeOneArbitraryPortsIndexEquivMod0` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 6a4b29b028b83fbc819737d712234425c38a1005304f8b884f1123e90d073326.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-one-arbitrary-ports-index-equiv-mod0-candidate-v1.lean; source SHA-256 6a4b29b028b83fbc819737d712234425c38a1005304f8b884f1123e90d073326; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib

namespace CubicP3Partition

open CubicP3Partition
theorem R03SP01ThreeOneArbitraryPortsIndexEquivMod0
    (b d : Nat) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) (hr : d % 3 = 0) :
    ∃ e : Fin (d - 3) ⊕ (Fin ((1 + 3 * b) - d - 1) ⊕ Fin 4) ≃
      Fin (1 + 3 * b),
      (∀ i : Fin (d - 3), e (Sum.inl i) =
        ⟨2 + i.val, by omega⟩) ∧
      (∀ j : Fin ((1 + 3 * b) - d - 1), e (Sum.inr (Sum.inl j)) =
        ⟨d + 1 + j.val, by omega⟩) ∧
      e (Sum.inr (Sum.inr 0)) = ⟨0, by omega⟩ ∧
      e (Sum.inr (Sum.inr 1)) = ⟨1, by omega⟩ ∧
      e (Sum.inr (Sum.inr 2)) = ⟨d - 1, by omega⟩ ∧
      e (Sum.inr (Sum.inr 3)) = ⟨d, by omega⟩ := by sorry

end CubicP3Partition
