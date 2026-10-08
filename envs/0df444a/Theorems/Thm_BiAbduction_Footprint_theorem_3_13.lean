-- Prove2me | Theorems.Thm_BiAbduction_Footprint_theorem_3_13
-- name    : BiAbduction.Footprint.theorem_3_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:01.949827+00:00
-- url     : https://prove2.me/theorems/e62cc729-a14d-41e1-a126-43db054661f6
-- title:
--   Theorem 3.13 — the unique ≾-minimal solution of F ∗ ? ⊨ G exists and is min(F −∗ G)
-- statement:
--   Let $F, G$ be arbitrary predicates (sets of stack–heap pairs, heaps finite). The abduction question $F * M \models G$ has a best solution with respect to the betterness order $\precsim$, namely
--   $$\min(F \mathbin{-\!\!*} G):$$
--   it is a solution, it satisfies $\min(F \mathbin{-\!\!*} G) \precsim M$ for every solution $M$ (every predicate $M$ with $F * M \models G$), and it is the only solution with this property.
--
--   This is the semantic answer to abduction against which the paper measures its algorithms, and Theorem 4.11 uses it to identify the anti-frames computed by an ideal bi-abductive prover.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 24, Theorem 3.13 (proof p. 25)

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics

namespace BiAbduction.Footprint

/-- Theorem 3.13 (p. 24): the minimal solution of `F ∗ ? ⊨ G` w.r.t. `≾` always exists and is
`min(F −∗ G)`; it is the only `≾`-least solution. -/
theorem theorem_3_13 (F G : Pred) :
    IsLeastSolution F G (minSet (wand F G)) ∧
    ∀ M : Pred, IsLeastSolution F G M → M = minSet (wand F G) := by sorry

end BiAbduction.Footprint
