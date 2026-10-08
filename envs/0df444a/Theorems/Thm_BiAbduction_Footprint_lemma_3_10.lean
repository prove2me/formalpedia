-- Prove2me | Theorems.Thm_BiAbduction_Footprint_lemma_3_10
-- name    : BiAbduction.Footprint.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:15.54678+00:00
-- url     : https://prove2.me/theorems/32b9001e-bfe3-4484-b0e5-8b669a02e5c2
-- title:
--   Lemma 3.10 — ≤ is a preorder, M ≤ min(M) ≤ M, and M, M′ are ≤-equivalent iff min(M) = min(M′)
-- statement:
--   Let $\le$ be the spatial preorder $M \le M' \iff M' \models M * \mathsf{true}$ on predicates (sets of stack–heap pairs with finite heaps), and let $\min$ be the minimal-state operator of Definition 3.9. Then:
--   1. $\le$ is a preorder (reflexive and transitive);
--   2. for every predicate $M$, $M \le \min(M)$ and $\min(M) \le M$;
--   3. for all predicates $M, M'$,
--   $$\big(M \le M' \text{ and } M' \le M\big) \iff \min(M) = \min(M').$$
--
--   The lemma shows that $\min$ picks a canonical representative of each $\le$-equivalence class, which is what makes the best abductive solution unique.
--
--   **Formalization Note** Part (1) is stated as reflexivity and transitivity of `SpatialLe` over all predicates. Finiteness of heaps is built into the heap type.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 24, Lemma 3.10

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics

namespace BiAbduction.Footprint

/-- Lemma 3.10 (p. 24), properties of `≤`: (1) `≤` is a preorder (reflexive and transitive);
for any `M, M'`, (2) `M ≤ min(M)` and `min(M) ≤ M`, and (3) `M ≤ M' ∧ M' ≤ M` iff
`min(M) = min(M')`. -/
theorem lemma_3_10 :
    ((∀ M : Pred, SpatialLe M M) ∧
      (∀ M₁ M₂ M₃ : Pred, SpatialLe M₁ M₂ → SpatialLe M₂ M₃ → SpatialLe M₁ M₃)) ∧
    ∀ M M' : Pred,
      (SpatialLe M (minSet M) ∧ SpatialLe (minSet M) M) ∧
      ((SpatialLe M M' ∧ SpatialLe M' M) ↔ minSet M = minSet M') := by sorry

end BiAbduction.Footprint
