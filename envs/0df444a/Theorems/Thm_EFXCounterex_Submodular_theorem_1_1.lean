-- Prove2me | Theorems.Thm_EFXCounterex_Submodular_theorem_1_1
-- name    : EFXCounterex.Submodular.theorem_1_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T00:45:36.362615+00:00
-- url     : https://prove2.me/theorems/5200c392-d795-4536-9ab9-ec4b1d12e26a
-- title:
--   Theorem 1.1 — three agents with weighted-coverage valuations over eight goods admit no EFX allocation
-- statement:
--   There is a valuation profile $w$ for three agents and eight goods in which every $w_i$ is a weighted-coverage valuation (finitely many features, nonnegative weights, a bundle worth the total weight of the features its goods cover) and no allocation (pairwise disjoint bundles covering all eight goods) is EFX for $w$. The paper proves it as the proof of Theorem 1.3 (p. 15) at $n=3$, $m=8$: Theorem 3.4, then the strictification of §3.2.2, then Lemma 3.7 (Lemma 3.5 is not needed).
--
--   Differences from the source:
--   - encoding: an allocation is a tuple of pairwise disjoint bundles whose union is M (empty bundles allowed, no unallocated goods) → X : Fin n → Finset (Fin m) with IsAllocation X := LittleCharity.EFX.IsPartialAllocation X ∧ LittleCharity.EFX.pool X = ∅; reason: pairwise disjoint plus empty pool (no unallocated good) is exactly 'union is M'
--   - encoding: "a fair division instance with three agents and eight goods in which all agents have weighted coverage valuations" → w : Fin 3 → Finset (Fin 8) → ℝ with IsWeightedCoverage (w i) for every i (features Fin k); reason: weighted-coverage values are nonnegative sums, so ℝ-valued is the same; any finite feature set is some Fin k
-- source:
--   Akrami, Mackenzie, Mayorov, Mehlhorn, Srinivas, Suzuki, Weidenbach 2026, Counterexamples to EFX for Submodular and Subadditive Valuations, arXiv:2605.06451 (supplied manuscript, sha256 700243a1…), Theorem 1.1, p. 2 (proof: proof of Theorem 1.3, p. 15)

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXCounterex_Submodular_Setting

namespace EFXCounterex.Submodular

/-- Theorem 1.1 (p. 2). There is a fair-division instance with three agents and eight goods in
which every agent has a weighted-coverage valuation and no (complete) allocation is EFX. -/
theorem theorem_1_1 :
    ∃ w : Fin 3 → Finset (Fin 8) → ℝ,
      (∀ i, IsWeightedCoverage (w i)) ∧
      ∀ X : Fin 3 → Finset (Fin 8), IsAllocation X → ¬ LittleCharity.EFX.IsEFX w X := by sorry

end EFXCounterex.Submodular
