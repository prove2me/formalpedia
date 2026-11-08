-- Prove2me | Theorems.Thm_BeliefDominance_theorem_3
-- name    : BeliefDominance.theorem_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:25:00.652138+00:00
-- url     : https://prove2.me/theorems/68ace0b6-fe0e-4882-b03b-ba6ac3258299
-- title:
--   Theorem 3 — weak consistency rules out fallacious inconsistency
-- statement:
--   Let $\preceq$ and $\preceq_{x_1,y}$ be relations on a two-period decision space. If they have the property of weak consistency, then they cannot exhibit fallacious inconsistency: for every $x^*\in X^*$ and every signal $y$,
--
--   $$
--   x_2^*(y)\in X^*_{2,x_1^*,y}.
--   $$
--
--   So under a weakly consistent ordering the decision-maker can always carry out an optimal plan.
--
--   Differences from the source:
--   - generalization: §3.2 assumes ≼ a preorder → arbitrary relations le and le₂; reason: preorders are a special case, and the printed proof does not use the assumption
--   - reading: the generic ≺ and ≺_{x₁,y} of §3.2–3.3 are not spelled out → strictPart le and strictPart (le₂ x₁ y); reason: for the preorder ≼ of §3.2 the strict relation is its strict part
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, Theorem 3, p.7; proof in Appendix B, p.11

import Mathlib
import Definitions.Def_BeliefDominance_DecisionSpace

namespace BeliefDominance

/-- Theorem 3: a preference ordering that has the property of weak consistency cannot exhibit
fallacious inconsistency (Ekholm–Baker, *Multiple Beliefs, Dominance and Dynamic Consistency*,
Management Science, doi:10.1287/mnsc.2020.3908, p.7 (PDF p.8); proof in Appendix B, p.11 (PDF
p.12)).

**Formalization Note** §3.2 assumes `≼` a preorder. The statement here does not, so it holds for
arbitrary relations and specializes to preorders. -/
theorem theorem_3 {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y)
    (le : A₁ × (Y → A₂) → A₁ × (Y → A₂) → Prop) (le₂ : A₁ → Y → A₂ → A₂ → Prop)
    (h : WeaklyConsistent D le le₂) : ¬ ExhibitsFallacious D le le₂ := by sorry

end BeliefDominance
