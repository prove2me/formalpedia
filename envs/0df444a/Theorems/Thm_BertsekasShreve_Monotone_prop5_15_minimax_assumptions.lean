-- Prove2me | Theorems.Thm_BertsekasShreve_Monotone_prop5_15_minimax_assumptions
-- name    : BertsekasShreve.Monotone.prop5_15_minimax_assumptions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:20:29.88342+00:00
-- url     : https://prove2.me/theorems/677414f9-bcd6-4d86-ba39-0ccd7cd039fd
-- title:
--   Proposition 5.15 — the minimax model satisfies I, I.1, I.2 or D, D.2, with scalar α
-- statement:
--   Let $W$ be a set, $W(x,u)\subseteq W$, $g : S\times C\times W\to[-\infty,\infty]$, $f : S\times C\times W\to S$ and $\alpha>0$. Consider an abstract monotone dynamic programming model on $S$, $C$ with constraint sets $U(x)$ such that $W(x,u)$ is nonempty for every $x\in S$, $u\in U(x)$, whose mapping is the minimax mapping
--   $$H(x,u,J)=\sup_{w\in W(x,u)}\bigl\{g(x,u,w)+\alpha J[f(x,u,w)]\bigr\}$$
--   (sums with $\infty-\infty=\infty$) and whose terminal function is $J_0(x)=0$ for all $x\in S$.
--
--   1. If
--   $$0\le g(x,u,w)\qquad\forall x\in S,\ u\in U(x),\ w\in W,$$
--   then Assumptions I, I.1 and I.2 are satisfied, with the scalar in I.2 equal to $\alpha$.
--   2. If
--   $$g(x,u,w)\le 0\qquad\forall x\in S,\ u\in U(x),\ w\in W,$$
--   then Assumptions D and D.2 are satisfied, with the scalar in D.2 equal to $\alpha$.
--
--   Assumption D.1 is absent from part 2: without further hypotheses the supremum does not commute with decreasing limits, which is why only part of the chapter's theory applies to minimax control under D.
--
--   **Formalization Note** Part 1 is stated for every `MonotoneDP.Increase.Model` and part 2 for every `MonotoneDP.Decrease.Model` whose fields are `H = BertsekasShreve.FiniteHorizon.minimaxH Wset g f α` (the shared definition of Section 2.3.5's mapping, sum taken with `badd`, i.e. $\infty-\infty=\infty$) and `Jbar ≡ 0`; such models exist because the mapping is monotone in $J$. The section's standing assumptions $\alpha>0$ and $W(x,u)\ne\varnothing$ are explicit hypotheses.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 90, Proposition 5.15; mapping from p. 38, Section 2.3.5, Eq. (29) of Chapter 2

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.Monotone

/-- Bertsekas & Shreve (1996), p. 90, Proposition 5.15: for the minimax mapping
`H(x, u, J) = sup_{w ∈ W(x, u)} {g(x, u, w) + α J[f(x, u, w)]}` of Section 2.3.5 (with `α > 0` and
`W(x, u)` nonempty for `x ∈ S`, `u ∈ U(x)`, the standing assumptions of that section) and
`J₀ ≡ 0`:
(a) if `0 ≤ g(x, u, w)` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W`, then I, I.1 and I.2 hold, the scalar
in I.2 being `α`;
(b) if `g(x, u, w) ≤ 0` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W`, then D and D.2 hold, the scalar in
D.2 being `α`. -/
theorem prop5_15_minimax_assumptions {S C W : Type*}
    (Wset : S → C → Set W) (g : S → C → W → EReal) (f : S → C → W → S) (α : ℝ) (hα : 0 < α) :
    (∀ m : MonotoneDP.Increase.Model S C, m.H = BertsekasShreve.FiniteHorizon.minimaxH Wset g f α → m.Jbar = (fun _ => 0) →
      (∀ x : S, ∀ u ∈ m.U x, (Wset x u).Nonempty) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 0 ≤ g x u w) →
        m.AssumptionI ∧ m.AssumptionI1 ∧ m.AssumptionI2 α) ∧
    (∀ m : MonotoneDP.Decrease.Model S C, m.H = BertsekasShreve.FiniteHorizon.minimaxH Wset g f α → m.Jbar = (fun _ => 0) →
      (∀ x : S, ∀ u ∈ m.U x, (Wset x u).Nonempty) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, g x u w ≤ 0) →
        m.AssumptionD ∧ m.AssumptionD2 α) := by sorry

end BertsekasShreve.Monotone
