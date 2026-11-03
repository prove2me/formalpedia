-- Prove2me | Theorems.Thm_BeliefDominance_le_isPreorder
-- name    : BeliefDominance.le_isPreorder
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:25:38.227298+00:00
-- url     : https://prove2.me/theorems/a3394db7-0a3d-4984-bceb-b898c3e154de
-- title:
--   §3.1 — the relations of belief dominance are preorders
-- statement:
--   For every decision problem with multiple beliefs, the first-period relation $\succeq$ is reflexive and transitive, belief dominance is its strict part, and indifference is its symmetric part:
--
--   $$
--   x'\succ x\iff x\preceq x'\ \text{and not}\ x'\preceq x,\qquad
--   x'\sim x\iff x\preceq x'\ \text{and}\ x'\preceq x.
--   $$
--
--   The same three facts hold for the second-period relation $\succeq_{x_1,y}$ at each $x_1$ and $y$.
--
--   This identifies the paper's direct definitions (3) and (4) with the generic strict and symmetric parts used in §3.2–3.3, so that the general theory applies to belief dominance.
--
--   Differences from the source:
--   - generalization: ≽ is stated to be a preorder for strategies, in the first period → the same for all pairs of A₁ × (Y → A₂), for the second-period relations too, and with ≻ and ~ identified as its strict and symmetric parts; reason: the first conjunct restricted to X is the source claim; the rest is what §3.2–3.3 needs to apply to belief dominance
--   - reading: ~_{x₁,y} and ≼_{x₁,y} are used on p.6 without a definition for belief dominance, and the generic ≺ of §3.2–3.3 is not spelled out → Indiff₂ is equality of V₂ on Φ_y, le₂ is Dominates₂ ∨ Indiff₂, and ≺ is strictPart; reason: analogy with the first-period definitions of p.5; le_isPreorder shows that dominance is exactly this strict part
--   - encoding: discrete random variables, with the iterated sum of (1) over 𝒴 and 𝒵 → beliefs PMF (Y × Z) on arbitrary types, with one sum over Y × Z; reason: same instances; the sums agree under WellPosed
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, §3.1, p.5

import Mathlib
import Definitions.Def_BeliefDominance_Problem

namespace BeliefDominance

/-- The relations of belief dominance are preorders, whose strict and symmetric parts are the
paper's dominance and indifference (Ekholm–Baker, *Multiple Beliefs, Dominance and Dynamic
Consistency*, Management Science, doi:10.1287/mnsc.2020.3908, §3.1, p.5 (PDF p.6)).

**Formalization Note** `le x x'` means `x ≼ x'`. The strict and symmetric parts are consequences
here, since `Dominates` and `Indiff` transcribe the paper's definitions. -/
theorem le_isPreorder {A₁ A₂ Y Z : Type*} (P : Problem A₁ A₂ Y Z) :
    ((∀ x, P.le x x) ∧
      (∀ x x' x'', P.le x x' → P.le x' x'' → P.le x x'') ∧
      (∀ x x', P.Dominates x' x ↔ strictPart P.le x x') ∧
      (∀ x x', P.Indiff x' x ↔ P.le x x' ∧ P.le x' x)) ∧
    ∀ (x₁ : A₁) (y : Y),
      (∀ a, P.le₂ x₁ y a a) ∧
      (∀ a a' a'', P.le₂ x₁ y a a' → P.le₂ x₁ y a' a'' → P.le₂ x₁ y a a'') ∧
      (∀ a a', P.Dominates₂ x₁ y a' a ↔ strictPart (P.le₂ x₁ y) a a') ∧
      (∀ a a', P.Indiff₂ x₁ y a' a ↔ P.le₂ x₁ y a a' ∧ P.le₂ x₁ y a' a) := by sorry

end BeliefDominance
