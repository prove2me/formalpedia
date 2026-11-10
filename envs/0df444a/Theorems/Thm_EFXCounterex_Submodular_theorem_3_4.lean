-- Prove2me | Theorems.Thm_EFXCounterex_Submodular_theorem_3_4
-- name    : EFXCounterex.Submodular.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:45:49.560107+00:00
-- url     : https://prove2.me/theorems/869fefb0-0a8e-420e-b9c3-56c4603de2e4
-- title:
--   Theorem 3.4 — the monotone valuations $v_a,v_b,v_c$ admit no EFX allocation
-- statement:
--   Each of the final valuations $v_a,v_b,v_c$ is monotone, and no allocation of the eight goods to the three agents is EFX for $v$.
--
--   Differences from the source:
--   - encoding: goods M = {A1, A2, B1, B2, C1, C2, x, y}, agents N = {a, b, c} associated with types A, B, C; type-words such as Px, QR, BCCx, UVx; values of u_i and v_i in {0, …, 7} → goods Fin 8 (A1, A2, B1, B2, C1, C2 = 0, …, 5; x = gx = 6; y = gy = 7) with kind : Fin 8 → GoodKind (typ 0, typ 1, typ 2 = A, B, C); agents Fin 3 (a, b, c = 0, 1, 2), agent t associated with type typ t; type-words as statements about the kinds of goods; u, v valued in ℝ; reason: a naming of the same finite sets and the same numbers
--   - encoding: an allocation is a tuple of pairwise disjoint bundles whose union is M (empty bundles allowed, no unallocated goods) → X : Fin n → Finset (Fin m) with IsAllocation X := LittleCharity.EFX.IsPartialAllocation X ∧ LittleCharity.EFX.pool X = ∅; reason: pairwise disjoint plus empty pool (no unallocated good) is exactly 'union is M'
--   - reading: "The three monotone valuations va, vb, vc admit no EFX allocation" → (∀ i, IsMonotone (v i)) ∧ ∀ X, IsAllocation X → ¬ IsEFX v X; reason: the adjective 'monotone' is asserted of v on p. 8 and is kept as a clause, the stronger reading
-- source:
--   Akrami, Mackenzie, Mayorov, Mehlhorn, Srinivas, Suzuki, Weidenbach 2026, Counterexamples to EFX for Submodular and Subadditive Valuations, arXiv:2605.06451 (supplied manuscript, sha256 700243a1…), Theorem 3.4, p. 10

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXCounterex_Submodular_Setting
import Definitions.Def_EFXCounterex_Submodular_Instance

namespace EFXCounterex.Submodular

/-- Theorem 3.4 (p. 10). The three valuations `v_a, v_b, v_c` are monotone and admit no EFX
allocation. -/
theorem theorem_3_4 :
    (∀ i : Fin 3, IsMonotone (v i)) ∧
      ∀ X : Fin 3 → Finset (Fin 8), IsAllocation X → ¬ LittleCharity.EFX.IsEFX v X := by sorry

end EFXCounterex.Submodular
