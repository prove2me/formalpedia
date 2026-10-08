-- Prove2me | Theorems.Thm_CondatPD_FinDim_solution_of_opP_stepT_eq
-- name    : CondatPD.FinDim.solution_of_opP_stepT_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:40:42.999373+00:00
-- url     : https://prove2.me/theorems/7c301b80-9e40-4e95-9674-954fff571f1a
-- title:
--   §4, proof of Theorem 3.3, p. 13, via (35) — if P T(z) = P z then T(z) solves (6) with F = 0
-- statement:
--   Let $G\in\Gamma_0(\mathcal X)$, $H\in\Gamma_0(\mathcal Y)$, $L:\mathcal X\to\mathcal Y$ bounded linear, $\tau>0$, $\sigma>0$, and let $T$, $P$ be as in the proof of Theorem 3.3. For every $z=(x,y)$, if
--   $$P\,T(z)=Pz,$$
--   then $T(z)=(\tilde x,\tilde y)$ solves (6) with $F=0$:
--   $$0\in\partial G(\tilde x)+L^*\tilde y,\qquad 0\in-L\tilde x+\partial H^*(\tilde y).$$
--
--   This is the second arrow of "$z\in\operatorname{fix}(T')\Rightarrow PT(z)=Pz\Rightarrow T(z)\in\operatorname{zer}(A)$", which rests on the inclusion (35), $0\in A(T(z))+PT(z)-Pz$.
--
--   **Formalization Note** Only the second arrow is stated; the first involves the projector $S$. No bound on $\sigma\tau\|L\|^2$ is needed. Finite dimension is not assumed.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 13, §4, proof of Theorem 3.3 for Algorithm 3.1, after (42), using (35) of p. 12

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting

open InnerProductSpace

namespace CondatPD.FinDim

/-- Proof of Theorem 3.3, via (35) (p. 13): if `P T(z) = P z`, then `T(z)` solves (6) with
`F = 0`, i.e. `T(z) ∈ zer(A)`. -/
theorem solution_of_opP_stepT_eq {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ)
    (PG : X → X) (PH : Y → Y)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (conj H) PH) :
    ∀ (x : X) (y : Y), opP τ σ L (stepT PG PH τ σ L (x, y)) = opP τ σ L (x, y) →
      IsPDSolution 0 G H L (stepT PG PH τ σ L (x, y)).1 (stepT PG PH τ σ L (x, y)).2 := by sorry

end CondatPD.FinDim
