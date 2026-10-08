-- Prove2me | Theorems.Thm_BiAbduction_Footprint_lemma_3_12
-- name    : BiAbduction.Footprint.lemma_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:54.352087+00:00
-- url     : https://prove2.me/theorems/f8724ef9-ed8a-4e90-91ad-8cc31ae65981
-- title:
--   Lemma 3.12 — F −∗ G is a minimal solution of F ∗ ? ⊨ G w.r.t. ≤
-- statement:
--   Let $F, G$ be predicates and consider the abduction question $F * M \models G$. Then $F \mathbin{-\!\!*} G$ is a solution, and it is $\le$-below every solution:
--   $$F * (F \mathbin{-\!\!*} G) \models G, \qquad F * M \models G \implies (F \mathbin{-\!\!*} G) \le M .$$
--   Moreover, as used in the proof, $\mathbin{-\!\!*}$ is right adjoint to $*$: for every predicate $M$,
--   $$F * M \models G \iff M \models F \mathbin{-\!\!*} G.$$
--
--   Since $\le$ is only a preorder, this minimal solution is not unique; Theorem 3.13 refines it to the unique $\precsim$-least solution.
--
--   **Formalization Note** "Minimal w.r.t. ≤" is stated as ≤-least (below every solution), which is how the paper uses it in the proof of Theorem 3.13 and which implies minimality. The adjunction is a third conjunct.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 24, Lemma 3.12 and its proof

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics

namespace BiAbduction.Footprint

/-- Lemma 3.12 (p. 24): `F −∗ G` is a solution of `F ∗ ? ⊨ G` and is `≤`-below every
solution; together with the adjunction used in its proof, `F ∗ M ⊨ G` iff `M ⊨ F −∗ G`. -/
theorem lemma_3_12 (F G : Pred) :
    IsSolution F G (wand F G) ∧
    (∀ M : Pred, IsSolution F G M → SpatialLe (wand F G) M) ∧
    (∀ M : Pred, IsSolution F G M ↔ Entails M (wand F G)) := by sorry

end BiAbduction.Footprint
