-- Prove2me | Theorems.Thm_DoubleMoralHazard_Baseline_lemma_4_case2
-- name    : DoubleMoralHazard.Baseline.lemma_4_case2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:37.179706+00:00
-- url     : https://prove2.me/theorems/8e8e448f-8735-43e2-812e-8e2c9a293072
-- title:
--   Lemma 4, p. 20 — if µpRᵘ < c < µRᵘ, the corrected (2.11) with F(0) = 0 has a unique solution F₂, concave, with F₂′ ≥ −1
-- statement:
--   Let the parameters of the baseline model satisfy the standing condition (2.5) and $\mu pR^u<c<\mu R^u$. Then the value-function equation (2.11), in the corrected form $rF(w)=r\bar V+\mu p[F(w+R^u)-F(w)]+\mu(1-p)[F(w+\beta^o)-F(w)]+r(w-\bar w^2)F'(w)$, with boundary condition $F(0)=0$ (in the solution sense of the file `HJB`: continuous on $[0,\infty)$, differentiable on $[0,\bar w^2)$, extended with slope $-1$ beyond $\bar w^2$) has a solution $F_2$, any two solutions agree on $[0,\infty)$, and
--   $$F_2\ \text{is concave on }[0,\infty),\qquad F_2\ \text{is differentiable on }[0,\infty),\qquad F_2'(w)\ge -1\quad (w\ge 0).$$
--
--   The function $F_2$ is the principal's value function in Scenario 2: Proposition 1 identifies it with the principal's utility under $\gamma^2(w)$ and Proposition 2 shows it bounds the principal's utility under every incentive compatible contract. Concavity with $F'\ge-1$ makes its maximizer $w^2$ over $w\ge0$ unique, which fixes the starting promised utility of the optimal contract.
--
--   **Formalization Note** Uniqueness is asserted on $[0,\infty)$ only, since values at negative arguments are not constrained by the equation. Differentiability on all of $[0,\infty)$, including at $\bar w^2$, is part of the conclusion because "$F'(w)\ge-1$" presupposes the derivative exists; at $w=0$ the derivative is one-sided. The standing condition (2.5) is part of the parameters; the lemma is false without it. The printed (2.11) has an extra $-rF(w)$ on its right-hand side; the corrected equation is the one obtained from the HJB equation (2.7) and used in the proofs (see the file `HJB`). The paper omits the proof of this case as similar to Scenario 1.
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), p. 20, Lemma 4 (second sentence), with (2.11), p. 16, corrected; proof omitted in Appendix B.4, p. 48

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_HJB

namespace DoubleMoralHazard.Baseline

open Set

/-- Lemma 4, p. 20, Scenario 2 (`µ p Rᵘ < c < µ Rᵘ`): the corrected equation (2.11) with `F(0) = 0` has a solution `F`
(extended with slope `-1` beyond the tenure threshold), unique on `[0, ∞)`, concave on `[0, ∞)`,
differentiable on `[0, ∞)` with `F' ≥ -1`. -/
theorem lemma_4_case2 (P : Params) (hcase : P.mu * P.p * P.Ru < P.c ∧ P.c < P.mu * P.Ru) :
    ∃ F : ℝ → ℝ, IsSol2 P F ∧
      (∀ G : ℝ → ℝ, IsSol2 P G → EqOn G F (Ici 0)) ∧
      ConcaveOn ℝ (Ici 0) F ∧
      DifferentiableOn ℝ F (Ici 0) ∧
      ∀ w : ℝ, 0 ≤ w → -1 ≤ derivWithin F (Ici 0) w := by sorry

end DoubleMoralHazard.Baseline
