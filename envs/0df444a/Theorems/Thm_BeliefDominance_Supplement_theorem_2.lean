-- Prove2me | Theorems.Thm_BeliefDominance_Supplement_theorem_2
-- name    : BeliefDominance.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:30:47.939751+00:00
-- url     : https://prove2.me/theorems/904a70c4-f1ad-4a36-9d23-f873e8788dd6
-- title:
--   Theorem 2 — for complete preorders, strong and weak consistency are equivalent
-- statement:
--   Consider a two-period decision space with strategy set $X$, first-period actions $X_1$ and second-period action sets $X_{2,x_1,y}$, a preference relation $\preceq$ on strategies and second-period preference relations $\preceq_{x_1,y}$. Assume that all of them are **complete preorders**:
--
--   1. $\preceq$ is reflexive and transitive on $X$, and $x\preceq x'$ or $x'\preceq x$ for all $x,x'\in X$;
--   2. for every $x_1\in X_1$ and every signal $y$, $\preceq_{x_1,y}$ is reflexive and transitive on $X_{2,x_1,y}$, and $a\preceq_{x_1,y}b$ or $b\preceq_{x_1,y}a$ for all $a,b\in X_{2,x_1,y}$.
--
--   **Theorem 2.** Under these assumptions,
--
--   $$
--   (\preceq,\preceq_{\cdot,\cdot})\ \text{is strongly consistent}\iff(\preceq,\preceq_{\cdot,\cdot})\ \text{is weakly consistent}.
--   $$
--
--   So the distinction between the two notions of dynamic consistency, and between the fallacious and fallible inconsistencies they rule out, arises only for incomplete preference orderings such as belief dominance.
--
--   **Formalization Note** `le x x'` means $x\preceq x'$ and `le₂ x₁ y a b` means $a\preceq_{x_1,y}b$. The paper's "complete preorders $\succeq$" is read as covering both periods: the printed proof rewrites $\hat x_2\not\prec_{\tilde x_1,y}\tilde x_2(y)$ as $\hat x_2\succeq_{\tilde x_1,y}\tilde x_2(y)$, which uses completeness of the second-period relation. With only $\preceq$ complete the equivalence fails: take one first-period action, one signal, second-period actions $\{a,b\}$, $\preceq$ the total order with $(\cdot,b)\prec(\cdot,a)$ and $\preceq_{x_1,y}$ equality; this is weakly but not strongly consistent.
--
--   Differences from the source:
--   - reading: complete preorders ≽ → ≼ is a complete preorder on X and, for every x₁ ∈ X₁ and every signal y, ≼_{x₁,y} is a complete preorder on X_{2,x₁,y}; reason: the printed proof uses completeness of ≼_{x̃₁,y} (x̂₂ ⊀ x̃₂(y) rewritten as x̂₂ ≽ x̃₂(y)), and with only ≼ complete the statement is false (one x₁, one signal, actions a, b, ≼ total with b ≺ a, ≼_{x₁,y} equality)
--   - encoding: the axioms hold on X and on each X_{2,x₁,y}, and nothing is assumed outside → order axioms quantified over D.strategies and D.X₂ x₁ y; reason: the relations compare elements of these sets only, so the instances are the same
--   - encoding: the strict and symmetric parts ≺, ∼ of §3.2–3.3 are written as symbols → strictPart le and le in both directions; reason: Lean convention; same instances
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, doi:10.1287/mnsc.2020.3908, Theorem 2 and its proof, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_BeliefDominance_DecisionSpace
import Definitions.Def_BeliefDominance_Supplement_StronglyConsistent

namespace BeliefDominance.Supplement

/-- Theorem 2: for complete preorders the two definitions of dynamic consistency are equivalent
(Ekholm–Baker, *Multiple Beliefs, Dominance and Dynamic Consistency*, Management Science,
doi:10.1287/mnsc.2020.3908, §3.3, p.6 (PDF p.7); proof on the same page).

**Formalization Note** "Complete preorders" is read for both periods, as the printed proof uses
completeness of `≼_{x̃₁,y}` when it rewrites `x̂₂ ⊀_{x̃₁,y} x̃₂(y)` as `x̂₂ ≽_{x̃₁,y} x̃₂(y)`:
`le` is reflexive, transitive and total on the strategy set `X`, and for every `x₁ ∈ X₁` and
every signal `y`, `le₂ x₁ y` is reflexive, transitive and total on `X_{2,x₁,y}`. -/
theorem theorem_2 {A₁ A₂ Y : Type*} (D : DecisionSpace A₁ A₂ Y)
    (le : A₁ × (Y → A₂) → A₁ × (Y → A₂) → Prop) (le₂ : A₁ → Y → A₂ → A₂ → Prop)
    (hrefl : ∀ x ∈ D.strategies, le x x)
    (htrans : ∀ x ∈ D.strategies, ∀ x' ∈ D.strategies, ∀ x'' ∈ D.strategies,
      le x x' → le x' x'' → le x x'')
    (htotal : ∀ x ∈ D.strategies, ∀ x' ∈ D.strategies, le x x' ∨ le x' x)
    (hrefl₂ : ∀ x₁ ∈ D.X₁, ∀ y : Y, ∀ a ∈ D.X₂ x₁ y, le₂ x₁ y a a)
    (htrans₂ : ∀ x₁ ∈ D.X₁, ∀ y : Y, ∀ a ∈ D.X₂ x₁ y, ∀ b ∈ D.X₂ x₁ y, ∀ c ∈ D.X₂ x₁ y,
      le₂ x₁ y a b → le₂ x₁ y b c → le₂ x₁ y a c)
    (htotal₂ : ∀ x₁ ∈ D.X₁, ∀ y : Y, ∀ a ∈ D.X₂ x₁ y, ∀ b ∈ D.X₂ x₁ y,
      le₂ x₁ y a b ∨ le₂ x₁ y b a) :
    StronglyConsistent D le le₂ ↔ WeaklyConsistent D le le₂ := by sorry

end BeliefDominance.Supplement
