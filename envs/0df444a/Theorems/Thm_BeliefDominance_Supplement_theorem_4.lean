-- Prove2me | Theorems.Thm_BeliefDominance_Supplement_theorem_4
-- name    : BeliefDominance.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:31:15.67848+00:00
-- url     : https://prove2.me/theorems/ed62893f-29f3-4341-92c1-257b49b3686f
-- title:
--   Theorem 4 — strong consistency rules out fallible inconsistency
-- statement:
--   Consider a two-period decision space with strategy set $X$, a preference relation $\preceq$ on strategies and second-period preference relations $\preceq_{x_1,y}$, with optimal sets $X^*$ (strategies $x^*$ with $x^*\not\prec x$ for all $x\in X$) and $X^*_{2,x_1,y}$ (actions $x_2^*\in X_{2,x_1,y}$ with $x_2^*\not\prec_{x_1,y}x_2$ for all $x_2\in X_{2,x_1,y}$).
--
--   The ordering exhibits **fallible inconsistency** if there are an optimal strategy $x^*\in X^*$, a signal $y$ and an action $x_2\in X^*_{2,x_1^*,y}$ such that every completion $(x_1^*,x_2,\hat x_2(Y\neq y))\in X$ is strictly worse than some strategy of $X$.
--
--   **Theorem 4.** If $(\preceq,\preceq_{\cdot,\cdot})$ is strongly consistent, then it does not exhibit fallible inconsistency.
--
--   Together with Theorem 3, this separates the two notions: weak consistency rules out only fallacious inconsistency, strong consistency rules out both.
--
--   **Formalization Note** No axiom is assumed on $\preceq$ or $\preceq_{x_1,y}$; the paper's standing preorder assumption is not needed. Fallible inconsistency is the published `ExhibitsFallible`, in which $x_1^*$ is the first-period action of some $x^*\in X^*$.
--
--   Differences from the source:
--   - generalization: §3.2 assumes ≼ is a preorder → no axiom on le or le₂; reason: the proof (Appendix B, p.11) uses none, and preorders are a special case
--   - reading: in the formula for fallible inconsistency x₁* is unbound → x₁* is the first-period action of some x* ∈ X* (the published ExhibitsFallible); reason: the sentence before the formula and clause (a) of the proof of Theorem 4 make it so
--   - encoding: the strict parts ≺, ≺_{x₁,y} of §3.2–3.3 are written as symbols → strictPart; reason: Lean convention; same instances
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, doi:10.1287/mnsc.2020.3908, Theorem 4, p.7 (PDF p.8); proof in Appendix B, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_BeliefDominance_DecisionSpace
import Definitions.Def_BeliefDominance_Supplement_StronglyConsistent

namespace BeliefDominance.Supplement

/-- Theorem 4: a preference ordering `≼` that has the property of strong consistency cannot
exhibit fallible inconsistency (Ekholm–Baker, *Multiple Beliefs, Dominance and Dynamic
Consistency*, Management Science, doi:10.1287/mnsc.2020.3908, §3.3, p.7 (PDF p.8); proof in
Appendix B, p.11 (PDF p.12)).

**Formalization Note** §3.2 assumes `≼` a preorder. The statement here assumes no axiom on `le`
or `le₂`, so it holds for arbitrary relations and specializes to preorders. Fallible
inconsistency is the published `ExhibitsFallible`, whose `x₁*` is the first-period action of an
optimal strategy `x* ∈ X*`. -/
theorem theorem_4 {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y)
    (le : A₁ × (Y → A₂) → A₁ × (Y → A₂) → Prop) (le₂ : A₁ → Y → A₂ → A₂ → Prop)
    (h : StronglyConsistent D le le₂) : ¬ ExhibitsFallible D le le₂ := by sorry

end BeliefDominance.Supplement
