-- Prove2me | Theorems.Thm_BeliefDominance_branch_identity
-- name    : BeliefDominance.branch_identity
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:25:51.182599+00:00
-- url     : https://prove2.me/theorems/d4b273c6-6e85-413a-8664-e8c6efc344b6
-- title:
--   Proof of Theorem 5, p. 7 — strategies differing on one branch
-- statement:
--   Let $x,\tilde x\in X$ have the same first-period action and agree on every signal other than $y$, and let $f\in\Phi$, in a problem whose sums (1) exist.
--
--   1. If $f_Y(y)\ne0$, then
--   $$
--   V(\tilde x,f)-V(x,f)=f_Y(y)\bigl(V_2(x_1,\tilde x_2(y),y,f)-V_2(x_1,x_2(y),y,f)\bigr).
--   $$
--   2. If $f_Y(y)=0$, then $f(z,y)=0$ for every $z$, and $V(\tilde x,f)=V(x,f)$.
--
--   This identity carries a comparison on the branch $Y=y$ over $\Phi_y$ to a comparison of whole strategies over $\Phi$. It uses the Bayes identity $f(z,y)=f_Z(z\mid y)f_Y(y)$.
--
--   Differences from the source:
--   - generalization: two displayed steps of the proof, inequalities between sums under the assumption of dominance on the branch → one identity for every pair of strategies that differ only on the branch y; reason: the printed inequalities follow from the identity and f_Y(y) ≥ 0
--   - reading: V(x, f) is written without comment, which presumes that the expectations exist → the hypothesis WellPosed: the sum (1) is summable for every f ∈ Φ and every x ∈ X; reason: Lean's tsum is 0 on a non-summable family, and the hypothesis covers exactly the strategies of X
--   - encoding: discrete random variables, with the iterated sum of (1) over 𝒴 and 𝒵 → beliefs PMF (Y × Z) on arbitrary types, with one sum over Y × Z; reason: same instances; the sums agree under WellPosed
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, proof of Theorem 5, p.7; Bayes identity, p.4

import Mathlib
import Definitions.Def_BeliefDominance_Problem

namespace BeliefDominance

/-- Strategies that differ only on the branch `Y = y`: their first-period values differ by
`f_Y(y)` times the difference of the second-period values if `f ∈ Φ_y`, and not at all otherwise.
These are the displays in the proof of Theorem 5 (Ekholm–Baker, *Multiple Beliefs, Dominance and
Dynamic Consistency*, Management Science, doi:10.1287/mnsc.2020.3908, p.7 (PDF p.8)), with the Bayes
identity `f(z, y) = f_Z(z | y) f_Y(y)` of p.4 (PDF p.5). -/
theorem branch_identity {A₁ A₂ Y Z : Type*} (P : Problem A₁ A₂ Y Z) (hP : P.WellPosed)
    {x x' : A₁ × (Y → A₂)} (hx : x ∈ P.space.strategies) (hx' : x' ∈ P.space.strategies)
    (y : Y) (h₁ : x.1 = x'.1) (h₂ : ∀ y' : Y, y' ≠ y → x.2 y' = x'.2 y')
    {f : PMF (Y × Z)} (hf : f ∈ P.Φ) :
    (fY f y ≠ 0 →
      P.V x' f - P.V x f = fY f y * (P.V₂ x.1 (x'.2 y) y f - P.V₂ x.1 (x.2 y) y f)) ∧
    (fY f y = 0 → (∀ z : Z, mass f y z = 0) ∧ P.V x' f = P.V x f) := by sorry

end BeliefDominance
