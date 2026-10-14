-- Prove2me | Theorems.Thm_DoubleMoralHazard_Baseline_lemma_4_case1
-- name    : DoubleMoralHazard.Baseline.lemma_4_case1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:15.065022+00:00
-- url     : https://prove2.me/theorems/36349cee-6ef0-444e-aeed-9121f7562b4d
-- title:
--   Lemma 4, p. 20 — if c ≤ µpRᵘ, (2.9) with F(0) = 0 has a unique solution F₁, concave, with F₁′ ≥ −1
-- statement:
--   Let the parameters of the baseline model satisfy the standing condition (2.5) and $c\le\mu pR^u$. Then the value-function equation (2.9), $rF(w)=r\bar V+\mu p[F(w+R^u)-F(w)]+r(w-\bar w^1)F'(w)$, with boundary condition $F(0)=0$ (in the solution sense of the file `HJB`: continuous on $[0,\infty)$, differentiable on $[0,\bar w^1)$, extended with slope $-1$ beyond $\bar w^1$) has a solution $F_1$, any two solutions agree on $[0,\infty)$, and
--   $$F_1\ \text{is concave on }[0,\infty),\qquad F_1\ \text{is differentiable on }[0,\infty),\qquad F_1'(w)\ge -1\quad (w\ge 0).$$
--
--   The function $F_1$ is the principal's value function in Scenario 1: Proposition 1 identifies it with the principal's utility under $\gamma^1(w)$ and Proposition 2 shows it bounds the principal's utility under every incentive compatible contract. Concavity with $F'\ge-1$ makes its maximizer $w^1$ over $w\ge0$ unique, which fixes the starting promised utility of the optimal contract.
--
--   **Formalization Note** Uniqueness is asserted on $[0,\infty)$ only, since values at negative arguments are not constrained by the equation. Differentiability on all of $[0,\infty)$, including at $\bar w^1$, is part of the conclusion because "$F'(w)\ge-1$" presupposes the derivative exists; at $w=0$ the derivative is one-sided. The standing condition (2.5) is part of the parameters; the lemma is false without it.
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), p. 20, Lemma 4 (first sentence); proof Appendix B.4, pp. 47–48

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_HJB

namespace DoubleMoralHazard.Baseline

open Set

/-- Lemma 4, p. 20, Scenario 1 (`c ≤ µ p Rᵘ`): equation (2.9) with `F(0) = 0` has a solution `F`
(extended with slope `-1` beyond the tenure threshold), unique on `[0, ∞)`, concave on `[0, ∞)`,
differentiable on `[0, ∞)` with `F' ≥ -1`. -/
theorem lemma_4_case1 (P : Params) (hcase : P.c ≤ P.mu * P.p * P.Ru) :
    ∃ F : ℝ → ℝ, IsSol1 P F ∧
      (∀ G : ℝ → ℝ, IsSol1 P G → EqOn G F (Ici 0)) ∧
      ConcaveOn ℝ (Ici 0) F ∧
      DifferentiableOn ℝ F (Ici 0) ∧
      ∀ w : ℝ, 0 ≤ w → -1 ≤ derivWithin F (Ici 0) w := by sorry

end DoubleMoralHazard.Baseline
