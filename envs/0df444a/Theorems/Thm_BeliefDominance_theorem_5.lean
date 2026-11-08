-- Prove2me | Theorems.Thm_BeliefDominance_theorem_5
-- name    : BeliefDominance.theorem_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:26:01.55908+00:00
-- url     : https://prove2.me/theorems/5c31d1a2-471d-457c-bfbd-5e28425ff744
-- title:
--   Theorem 5 — belief dominance is weakly consistent
-- statement:
--   Let a decision problem with a set $\Phi$ of discrete beliefs be given, whose sums (1) exist. If $x,\tilde x\in X$ have $x_1=\tilde x_1$ and agree on every signal other than $y$, then
--
--   $$
--   x_2(y)\prec_{x_1,y}\tilde x_2(y)\ \Longrightarrow\ x\prec\tilde x,\qquad
--   x_2(y)\preceq_{x_1,y}\tilde x_2(y)\ \Longrightarrow\ x\preceq\tilde x.
--   $$
--
--   So a second-period preference over $\Phi_y$ extends to the whole plan over $\Phi$, with no recursive formulation and no condition on $\Phi$.
--
--   Differences from the source:
--   - generalization: §3.4 takes "each possible signal y ∈ 𝒴" to have a positive probability mass → not assumed: a belief of Φ may give y mass 0, and Φ_y may be empty; reason: the printed proof itself treats f ∈ Φ with f_Y(y) = 0, and the source's case is the one where no such f occurs; the §3.4 remark on zero-probability signals under expected utility concerns a second-period preference outside eq. (4), since here Φ_y = ∅ makes all actions indifferent
--   - reading: V(x, f) is written without comment, which presumes that the expectations exist → the hypothesis WellPosed: the sum (1) is summable for every f ∈ Φ and every x ∈ X; reason: Lean's tsum is 0 on a non-summable family, and the hypothesis covers exactly the strategies of X
--   - reading: ~_{x₁,y} and ≼_{x₁,y} are used on p.6 without a definition for belief dominance, and the generic ≺ of §3.2–3.3 is not spelled out → Indiff₂ is equality of V₂ on Φ_y, le₂ is Dominates₂ ∨ Indiff₂, and ≺ is strictPart; reason: analogy with the first-period definitions of p.5; le_isPreorder shows that dominance is exactly this strict part
--   - encoding: discrete random variables, with the iterated sum of (1) over 𝒴 and 𝒵 → beliefs PMF (Y × Z) on arbitrary types, with one sum over Y × Z; reason: same instances; the sums agree under WellPosed
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, Theorem 5, p.7

import Mathlib
import Definitions.Def_BeliefDominance_Problem

namespace BeliefDominance

/-- Theorem 5: belief dominance is weakly consistent (Ekholm–Baker, *Multiple Beliefs, Dominance and
Dynamic Consistency*, Management Science, doi:10.1287/mnsc.2020.3908, p.7 (PDF p.8)).

**Formalization Note** Beliefs are discrete, as in the paper's proof. `Φ` is an arbitrary set, and a
belief of `Φ` may give the signal `y` mass 0. `WellPosed` says that the sums (1) exist. -/
theorem theorem_5 {A₁ A₂ Y Z : Type*} (P : Problem A₁ A₂ Y Z) (hP : P.WellPosed) :
    WeaklyConsistent P.space P.le P.le₂ := by sorry

end BeliefDominance
