-- Prove2me | Theorems.Thm_CarbonDoubleCount_Planner_eq_18
-- name    : CarbonDoubleCount.Planner.eq_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:32.527492+00:00
-- url     : https://prove2.me/theorems/e8b9ee84-90af-47e0-8679-50f69c736db3
-- title:
--   Equation (18), p. 25 — vanishing of each process contribution without double counting
-- statement:
--   Fix an interior feasible effort profile $e^*$, differentiable process footprints decreasing in each effort coordinate, and a differentiable carbon-payment rule $h$ increasing in every footprint coordinate. If the aggregate marginal payment for each process at $f(e^*)$ is at most the social carbon price $p_S$, and the first equality of (14) holds for each firm and action, then every summand vanishes:
--   $$
--   \frac{\partial f_i}{\partial e_{n,j}}(e^*)
--     \left(\frac{\partial h_n}{\partial f_i}(f(e^*))-p_S\right)=0
--     \qquad\text{for all }i,n,j.
--   $$
--   Equation (18) is the pointwise marginal relation used to obtain the contradiction for a jointly produced process.
--
--   **Formalization Note** The upper bound on aggregate marginal payment is equation (17) at the first-best footprint. The source's $m_{n_i}$ in (18) is read as the number $m_n$ of actions available to firm $n$.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, pp. 24–25, proof of Proposition 2, equations (17)–(18); https://www.anderson.ucla.edu/documents/areas/fac/dotm/bio/pdf_FC16.pdf

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_Setting

namespace CarbonDoubleCount.Planner

variable {ι : Type} {act : ι → Type} {κ : Type}
variable [Fintype ι] [DecidableEq ι]
variable [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
variable [Fintype κ] [DecidableEq κ]

/-- Display (18) of the proof of Proposition 2. -/
theorem eq_18
    (A pS : ℝ) (hA : 0 < A) (hpS : 0 < pS)
    (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (hfdiff : ∀ i, Differentiable ℝ (fun e => f e i))
    (hfanti : ∀ i, AntitoneOn (fun e => f e i) (effortBox A))
    (estar : (n : ι) → act n → ℝ)
    (hebox : estar ∈ effortBox A)
    (hint : ∀ n j, 0 < estar n j ∧ estar n j < A)
    (h : ι → (κ → ℝ) → ℝ)
    (hdiff : ∀ n, Differentiable ℝ (h n))
    (hmono : ∀ n, Monotone (h n))
    (h17 : ∀ i, (∑ n, dFoot (h n) (f estar) i) ≤ pS)
    (h14 : ∀ n j,
      (∑ i, dEff (fun e => f e i) estar n j *
        (dFoot (h n) (f estar) i - pS)) = 0) :
    ∀ i n j,
      dEff (fun e => f e i) estar n j *
        (dFoot (h n) (f estar) i - pS) = 0 := by sorry

end CarbonDoubleCount.Planner
