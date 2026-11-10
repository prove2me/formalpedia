-- Prove2me | Theorems.Thm_EFXCounterex_Submodular_lemma_3_3
-- name    : EFXCounterex.Submodular.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:45:43.501939+00:00
-- url     : https://prove2.me/theorems/c4ccbe05-9608-4d85-87da-bf4adf8afb4a
-- title:
--   Lemma 3.3 — in an EFX allocation for $v$ no agent holds its exceptional triple, and the allocation is EFX for $u$
-- statement:
--   For every allocation $X$ of the instance that is EFX for the final valuations $v$: (i) for every agent $i$, the bundle $X_i$ contains no exceptional triple of $i$; and (ii) $X$ is also EFX for the pair valuations $u$.
--
--   Differences from the source:
--   - encoding: goods M = {A1, A2, B1, B2, C1, C2, x, y}, agents N = {a, b, c} associated with types A, B, C; type-words such as Px, QR, BCCx, UVx; values of u_i and v_i in {0, …, 7} → goods Fin 8 (A1, A2, B1, B2, C1, C2 = 0, …, 5; x = gx = 6; y = gy = 7) with kind : Fin 8 → GoodKind (typ 0, typ 1, typ 2 = A, B, C); agents Fin 3 (a, b, c = 0, 1, 2), agent t associated with type typ t; type-words as statements about the kinds of goods; u, v valued in ℝ; reason: a naming of the same finite sets and the same numbers
--   - encoding: an allocation is a tuple of pairwise disjoint bundles whose union is M (empty bundles allowed, no unallocated goods) → X : Fin n → Finset (Fin m) with IsAllocation X := LittleCharity.EFX.IsPartialAllocation X ∧ LittleCharity.EFX.pool X = ∅; reason: pairwise disjoint plus empty pool (no unallocated good) is exactly 'union is M'
--   - encoding: "no agent receives a bundle containing its exceptional triple" → ∀ i, ¬ ∃ T ⊆ X i, IsExceptionalTriple i T (T has three goods, contains x and a good of each type other than i's); reason: a triple of type UVx is exactly such a T
-- source:
--   Akrami, Mackenzie, Mayorov, Mehlhorn, Srinivas, Suzuki, Weidenbach 2026, Counterexamples to EFX for Submodular and Subadditive Valuations, arXiv:2605.06451 (supplied manuscript, sha256 700243a1…), Lemma 3.3, p. 10

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXCounterex_Submodular_Setting
import Definitions.Def_EFXCounterex_Submodular_Instance

namespace EFXCounterex.Submodular

/-- Lemma 3.3 (p. 10). In an EFX allocation for the final valuations `v`, no agent receives a
bundle containing its exceptional triple; consequently the allocation is also EFX for the pair
valuations `u`. -/
theorem lemma_3_3 (X : Fin 3 → Finset (Fin 8)) (hX : IsAllocation X)
    (hEFX : LittleCharity.EFX.IsEFX v X) :
    (∀ i : Fin 3, ¬ ∃ T ⊆ X i, IsExceptionalTriple i T) ∧ LittleCharity.EFX.IsEFX u X := by sorry

end EFXCounterex.Submodular
