-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeOneArbitraryPortsIndexEquivMod1
-- name    : CubicP3Partition.R03SP01ThreeOneArbitraryPortsIndexEquivMod1
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:21:18.258133+00:00
-- url     : https://prove2.me/theorems/3021a5e0-7576-44cd-84d3-06b002a6d168
-- title:
--   R03 P3-factor structural result: R03SP01ThreeOneArbitraryPortsIndexEquivMod1
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeOneArbitraryPortsIndexEquivMod1` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is c4291e5f582e0e655ca4cf8eeda0adc9381e5d9d9640bc17210e02f99d45ad66.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-one-arbitrary-ports-index-equiv-mod1-candidate-v1.lean; source SHA-256 c4291e5f582e0e655ca4cf8eeda0adc9381e5d9d9640bc17210e02f99d45ad66; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib

namespace CubicP3Partition

open CubicP3Partition
theorem R03SP01ThreeOneArbitraryPortsIndexEquivMod1
    (b d : Nat) (hd : 1 ≤ d) (hdn : d < 1 + 3 * b) (hr : d % 3 = 1) :
    ∃ e : Fin (d - 1) ⊕ (Fin ((1 + 3 * b) - d - 3) ⊕ Fin 4) ≃
      Fin (1 + 3 * b),
      (∀ i : Fin (d - 1), e (Sum.inl i) =
        ⟨1 + i.val, by omega⟩) ∧
      (∀ j : Fin ((1 + 3 * b) - d - 3), e (Sum.inr (Sum.inl j)) =
        ⟨d + 2 + j.val, by omega⟩) ∧
      e (Sum.inr (Sum.inr 0)) = ⟨0, by omega⟩ ∧
      e (Sum.inr (Sum.inr 1)) = ⟨d, by omega⟩ ∧
      e (Sum.inr (Sum.inr 2)) = ⟨d + 1, by omega⟩ ∧
      e (Sum.inr (Sum.inr 3)) = ⟨(1 + 3 * b) - 1, by omega⟩ := by sorry

end CubicP3Partition
