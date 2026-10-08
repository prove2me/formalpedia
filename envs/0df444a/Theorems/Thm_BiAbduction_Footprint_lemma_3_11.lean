-- Prove2me | Theorems.Thm_BiAbduction_Footprint_lemma_3_11
-- name    : BiAbduction.Footprint.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:53.503971+00:00
-- url     : https://prove2.me/theorems/357ce38f-9d57-4436-b1f6-c0af7286912a
-- title:
--   Lemma 3.11 — ≾ is a partial order, and M′ ≤ M implies min(M′) ≾ M
-- statement:
--   Let $\le$ be the spatial preorder and $\precsim$ the betterness order on predicates,
--   $$M \precsim M' \iff (M \le M' \wedge M' \not\le M) \vee (M \le M' \wedge M' \le M \wedge M \models M').$$
--   Then:
--   1. $\precsim$ is a partial order: reflexive, transitive and antisymmetric (antisymmetry being equality of predicates as sets of states);
--   2. for all predicates $M, M'$, if $M' \le M$ then $\min(M') \precsim M$; in particular $\min(M) \precsim M$.
--
--   Part (2) is the step that turns a $\le$-least solution of an abduction question into the $\precsim$-least one.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 24, Lemma 3.11

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics

namespace BiAbduction.Footprint

/-- Lemma 3.11 (p. 24), properties of `≾`: (1) `≾` is a partial order (reflexive, transitive,
antisymmetric); for any `M, M'`, (2) `M' ≤ M` implies `min(M') ≾ M`; in particular
`min(M) ≾ M`. -/
theorem lemma_3_11 :
    ((∀ M : Pred, Better M M) ∧
      (∀ M₁ M₂ M₃ : Pred, Better M₁ M₂ → Better M₂ M₃ → Better M₁ M₃) ∧
      (∀ M₁ M₂ : Pred, Better M₁ M₂ → Better M₂ M₁ → M₁ = M₂)) ∧
    ∀ M M' : Pred,
      (SpatialLe M' M → Better (minSet M') M) ∧ Better (minSet M) M := by sorry

end BiAbduction.Footprint
