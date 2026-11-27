-- Prove2me | Theorems.Thm_BeliefDominance_Supplement_theorem_1
-- name    : BeliefDominance.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:30:14.576344+00:00
-- url     : https://prove2.me/theorems/50683b49-c721-5816-a701-e63b1925e6db
-- title:
--   Theorem 1 — strong consistency implies weak consistency
-- statement:
--   Consider a two-period decision space with strategy set $X$, a preference relation $\preceq$ on strategies and second-period preference relations $\preceq_{x_1,y}$. Assume, as throughout §3.2 of the paper, that $\preceq$ is a preorder on $X$: $x\preceq x$ for every $x\in X$, and $x\preceq x'$, $x'\preceq x''$ imply $x\preceq x''$ for $x,x',x''\in X$. The second-period relations are arbitrary.
--
--   **Theorem 1.** If $(\preceq,\preceq_{\cdot,\cdot})$ is strongly consistent, then it is weakly consistent: whenever $x,\tilde x\in X$ have $x_1=\tilde x_1$ and $x_2(Y\neq y)=\tilde x_2(Y\neq y)$ for some signal $y$,
--
--   $$
--   x_2(y)\prec_{x_1,y}\tilde x_2(y)\ \Longrightarrow\ x\prec\tilde x,
--   \qquad
--   x_2(y)\preceq_{x_1,y}\tilde x_2(y)\ \Longrightarrow\ x\preceq\tilde x .
--   $$
--
--   Strong consistency thus refines the usual notion of dynamic consistency (weak consistency), and so inherits its immunity to fallacious inconsistency (Theorem 3).
--
--   **Formalization Note** `le x x'` means $x\preceq x'$, `le₂ x₁ y a b` means $a\preceq_{x_1,y}b$, and the strict relations are `strictPart`. Reflexivity and transitivity are required for strategies of $X$ only.
--
--   Differences from the source:
--   - encoding: ≼ is a preorder on strategies → reflexivity and transitivity are assumed for strategies of X, and nothing is assumed outside X; reason: ≼ is a relation between strategies of X, so the instances are the same
--   - encoding: the strict and symmetric parts ≺, ∼ of §3.2–3.3 are written as symbols → strictPart le and le in both directions; reason: Lean convention; same instances
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, doi:10.1287/mnsc.2020.3908, Theorem 1, p.6 (PDF p.7); proof p.6 and Appendix B, p.11 (PDF p.12); preorder assumption §3.2, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_BeliefDominance_DecisionSpace
import Definitions.Def_BeliefDominance_Supplement_StronglyConsistent

namespace BeliefDominance.Supplement

/-- Theorem 1: strong consistency implies weak consistency (Ekholm–Baker, *Multiple Beliefs,
Dominance and Dynamic Consistency*, Management Science, doi:10.1287/mnsc.2020.3908, §3.3, p.6
(PDF p.7); proof p.6 and Appendix B, p.11 (PDF pp.7, 12)).

**Formalization Note** The standing assumption of §3.2 (p.5, PDF p.6) that `≼` is a preorder is
stated on the strategy set `X` only: `le x x` and transitivity for strategies of `X`. The
second-period relations `le₂` are arbitrary, as in the paper. -/
theorem theorem_1 {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y)
    (le : A₁ × (Y → A₂) → A₁ × (Y → A₂) → Prop) (le₂ : A₁ → Y → A₂ → A₂ → Prop)
    (hrefl : ∀ x ∈ D.strategies, le x x)
    (htrans : ∀ x ∈ D.strategies, ∀ x' ∈ D.strategies, ∀ x'' ∈ D.strategies,
      le x x' → le x' x'' → le x x'')
    (h : StronglyConsistent D le le₂) : WeaklyConsistent D le le₂ := by sorry

end BeliefDominance.Supplement
