-- Prove2me | Theorems.Thm_EFXCounterex_Submodular_proposition_3_2
-- name    : EFXCounterex.Submodular.proposition_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:45:37.863459+00:00
-- url     : https://prove2.me/theorems/68b7ab6e-c4d1-4bc5-97b2-2124e403ffd1
-- title:
--   Proposition 3.2 — the forced allocation: the EFX allocations for $u$ are exactly the relabellings of $Ay\mid BCCx\mid AB$
-- statement:
--   For every bundle profile $X$ of the instance: $X$ is an allocation that is EFX for the pair valuations $u$ if and only if, for some permutation $\sigma$ of the agents (acting simultaneously on their associated types and fixing $x,y$) and some choice of copies, $X_{\sigma(a)}$ is one $\sigma(A)$-good with $y$, $X_{\sigma(b)}$ is one $\sigma(B)$-good with both $\sigma(C)$-goods and $x$, and $X_{\sigma(c)}$ is the other $\sigma(A)$-good with the other $\sigma(B)$-good (`IsForcedAllocation X`). Both directions are asserted.
--
--   Differences from the source:
--   - encoding: goods M = {A1, A2, B1, B2, C1, C2, x, y}, agents N = {a, b, c} associated with types A, B, C; type-words such as Px, QR, BCCx, UVx; values of u_i and v_i in {0, …, 7} → goods Fin 8 (A1, A2, B1, B2, C1, C2 = 0, …, 5; x = gx = 6; y = gy = 7) with kind : Fin 8 → GoodKind (typ 0, typ 1, typ 2 = A, B, C); agents Fin 3 (a, b, c = 0, 1, 2), agent t associated with type typ t; type-words as statements about the kinds of goods; u, v valued in ℝ; reason: a naming of the same finite sets and the same numbers
--   - encoding: an allocation is a tuple of pairwise disjoint bundles whose union is M (empty bundles allowed, no unallocated goods) → X : Fin n → Finset (Fin m) with IsAllocation X := LittleCharity.EFX.IsPartialAllocation X ∧ LittleCharity.EFX.pool X = ∅; reason: pairwise disjoint plus empty pool (no unallocated good) is exactly 'union is M'
--   - reading: "Up to simultaneously relabelling types and agents, the EFX allocations for u are exactly Ay (agent a) | BCCx (agent b) | AB (agent c)" → (IsAllocation X ∧ IsEFX u X) ↔ IsForcedAllocation X, where IsForcedAllocation quantifies over a permutation σ of Fin 3 (agent σ t receives the role of agent t and type typ (σ t) that of typ t) and over the copies a₁ ≠ a₂ of type σ 0, b₁ ≠ b₂ of type σ 1; reason: relabelling acts on agents and their types simultaneously and fixes x, y (p. 8); the type-word notation leaves free which copy of a type goes where, since copies are interchangeable (§3.1.1)
-- source:
--   Akrami, Mackenzie, Mayorov, Mehlhorn, Srinivas, Suzuki, Weidenbach 2026, Counterexamples to EFX for Submodular and Subadditive Valuations, arXiv:2605.06451 (supplied manuscript, sha256 700243a1…), Proposition 3.2, p. 9

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXCounterex_Submodular_Setting
import Definitions.Def_EFXCounterex_Submodular_Instance

namespace EFXCounterex.Submodular

/-- Proposition 3.2 (the forced allocation, p. 9). Up to simultaneously relabelling types and
agents (and choosing which copy of a type goes where), the EFX allocations for the pair
valuations `u` are exactly `Ay (agent a) | BCCx (agent b) | AB (agent c)`: a bundle profile
`X` is a (complete) allocation that is EFX for `u` if and only if it has the forced shape. -/
theorem proposition_3_2 (X : Fin 3 → Finset (Fin 8)) :
    (IsAllocation X ∧ LittleCharity.EFX.IsEFX u X) ↔ IsForcedAllocation X := by sorry

end EFXCounterex.Submodular
