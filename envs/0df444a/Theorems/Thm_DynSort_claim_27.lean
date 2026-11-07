-- Prove2me | Theorems.Thm_DynSort_claim_27
-- name    : DynSort.claim_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:44.212637+00:00
-- url     : https://prove2.me/theorems/2d32e528-4ecd-46de-a0ac-e2bca1eaf6d8
-- title:
--   Claim 27 — Delete maintains the invariants and moves the hole to the end of the A-DST
-- statement:
--   Let $A$ be an A-DST reachable from the initial one by deletion–insertion pairs, of level $d$, and let $x$ be an element stored in $A$. After Delete $(x)$:
--
--   1. every component $D_j$ ($1\le j\le d$) satisfies the level-$j$ structural invariants, has at most one hole and at most $24\cdot2^{j-1}$ cells;
--   2. Suffix Sizes holds: for every $1\le j<d$, the components $D_j,\dots,A_1$ have at most $2^j$ cells in total, the hole included;
--   3. the array has exactly one hole, and it is its last cell;
--   4. the stored elements are those of $A$ other than $x$.
--
--   **Formalization Note** Suffix Sizes depends on the Re-Sort schedule, not on the invariants alone (p.56), so the claim is stated for reachable A-DSTs. Sizes count cells, the hole included, as in the proof (p.56).
--
--   Differences from the source:
--   - encoding: the Delete operation on an A-DST → Delete on an A-DST reachable from the initialization of p.6 by deletion–insertion pairs; reason: the invariants of an A-DST hold at reachable states, and Suffix Sizes is proved from the schedule (p.56)
--   - encoding: Suffix Sizes: A_j contains at most 2^j elements (p.23) → the components D_j, …, A₁ have at most 2^j cells, the hole included; reason: the proof counts all cells including holes (p.56); between updates there is no hole, so cells are elements
--   - generalization: maintains all structural invariants → also: at most one hole and at most 24·2^{j−1} cells per component, and the stored elements are those of A except x; reason: dropping these gives the source's claim
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claim 27, p.25 (PDF p.27); proof p.56 (PDF p.58)

import Mathlib
import Definitions.Def_DynSort_Inv
import Definitions.Def_DynSort_ADST

namespace DynSort

/-- **Claim 27**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §5.3, p.25 (PDF p.27; proof p.56): "The Delete operation maintains all
structural invariants and moves the resulting hole to the last position of the A-DST."

**Formalization Note.** `A` is any A-DST reached from the initial one by deletion–insertion pairs
(the Suffix Sizes bound rests on the Re-Sort schedule, p.56), and `x` is stored in it. After
Delete (x): every component `D_j` satisfies the invariants and the capacity, Suffix Sizes holds
(`|A_j| ≤ 2^j` for `j < d`, counting cells, the hole included, p.56), the array has exactly one
hole, it is the last cell, and the stored elements are those of `A` except `x`. -/
theorem claim_27 (n : ℕ) (A : ADST Elt) (hA : Reachable n A) (x : Elt) (hx : x ∈ A.stored) :
    let B := A.delete x
    (∀ j, 1 ≤ j → j ≤ B.d → RootInv j (B.comp j)) ∧
      (∀ j, 1 ≤ j → j < B.d → ((List.range j).map (fun k => (B.comp (k + 1)).size)).sum ≤ 2 ^ j) ∧
      B.holes = 1 ∧ B.flat.getLast? = some none ∧ B.stored.Perm (A.stored.erase x) := by sorry

end DynSort
