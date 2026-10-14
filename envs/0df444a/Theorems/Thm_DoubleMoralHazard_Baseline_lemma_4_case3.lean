-- Prove2me | Theorems.Thm_DoubleMoralHazard_Baseline_lemma_4_case3
-- name    : DoubleMoralHazard.Baseline.lemma_4_case3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:22.38649+00:00
-- url     : https://prove2.me/theorems/b21b74d8-a310-4358-9f7b-3cc794c0a371
-- title:
--   Lemma 4, p. 20 — if c ≥ µRᵘ, (2.13) with F(0) = 0 has a unique solution F₃, concave, with F₃′ ≥ −1
-- statement:
--   Let the parameters of the baseline model satisfy the standing condition (2.5) and $c\ge\mu R^u$. Then the value-function equation (2.13), $0=r\bar V+\mu[F(w+\beta)-F(w)]-rF(w)+r(w-\bar w^3)F'(w)$, with boundary condition $F(0)=0$ (in the solution sense of the file `HJB`: continuous on $[0,\infty)$, differentiable on $[0,\bar w^3)$, extended with slope $-1$ beyond $\bar w^3$) has a solution $F_3$, any two solutions agree on $[0,\infty)$, and
--   $$F_3\ \text{is concave on }[0,\infty),\qquad F_3\ \text{is differentiable on }[0,\infty),\qquad F_3'(w)\ge -1\quad (w\ge 0).$$
--
--   The function $F_3$ is the principal's value function in Scenario 3: Proposition 1 identifies it with the principal's utility under $\gamma^3(w)$ and Proposition 2 shows it bounds the principal's utility under every incentive compatible contract. Concavity with $F'\ge-1$ makes its maximizer $w^3$ over $w\ge0$ unique, which fixes the starting promised utility of the optimal contract.
--
--   **Formalization Note** Uniqueness is asserted on $[0,\infty)$ only, since values at negative arguments are not constrained by the equation. Differentiability on all of $[0,\infty)$, including at $\bar w^3$, is part of the conclusion because "$F'(w)\ge-1$" presupposes the derivative exists; at $w=0$ the derivative is one-sided. The standing condition (2.5) is part of the parameters; the lemma is false without it. The paper omits the proof of this case as similar to Scenario 1.
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), p. 20, Lemma 4 (third sentence); proof omitted in Appendix B.4, p. 48

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_HJB

namespace DoubleMoralHazard.Baseline

open Set

/-- Lemma 4, p. 20, Scenario 3 (`c ≥ µ Rᵘ`): equation (2.13) with `F(0) = 0` has a solution `F`
(extended with slope `-1` beyond the tenure threshold), unique on `[0, ∞)`, concave on `[0, ∞)`,
differentiable on `[0, ∞)` with `F' ≥ -1`. -/
theorem lemma_4_case3 (P : Params) (hcase : P.mu * P.Ru ≤ P.c) :
    ∃ F : ℝ → ℝ, IsSol3 P F ∧
      (∀ G : ℝ → ℝ, IsSol3 P G → EqOn G F (Ici 0)) ∧
      ConcaveOn ℝ (Ici 0) F ∧
      DifferentiableOn ℝ F (Ici 0) ∧
      ∀ w : ℝ, 0 ≤ w → -1 ≤ derivWithin F (Ici 0) w := by sorry

end DoubleMoralHazard.Baseline
