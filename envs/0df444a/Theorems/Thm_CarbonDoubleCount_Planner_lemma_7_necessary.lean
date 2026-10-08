-- Prove2me | Theorems.Thm_CarbonDoubleCount_Planner_lemma_7_necessary
-- name    : CarbonDoubleCount.Planner.lemma_7_necessary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:35.848963+00:00
-- url     : https://prove2.me/theorems/8bbe3209-354f-4e32-8a03-85eac880b64a
-- title:
--   Lemma 7, p. 24 — necessary marginal-payment condition (14)
-- statement:
--   Let $e^*$ be an interior social first best for firms with differentiable, concave, decreasing profits $V_n$ and differentiable, convex, decreasing, nonnegative process footprints $f_i$. The influence indicators $b_{n,i}\in\{0,1\}$ record whether firm $n$'s total marginal effect on process $i$ is negative throughout the effort box. If a differentiable carbon-payment rule $h_n$ makes $e^*$ a Nash equilibrium, then, for every firm $n$ and its action $j$,
--   $$
--   \sum_i\frac{\partial f_i}{\partial e_{n,j}}(e^*)
--     \left(\frac{\partial h_n}{\partial f_i}(f(e^*))-p_S\right)
--   =
--   \sum_i\frac{\partial f_i}{\partial e_{n,j}}(e^*)
--     \left(\frac{\partial h_n}{\partial f_i}(f(e^*))-p_S b_{n,i}\right)
--   =0.
--   $$
--   This is equation (14), the necessary condition used in the proof of the double-counting result.
--
--   **Formalization Note** The first best is a global maximizer on the effort box and Nash equilibrium uses all feasible unilateral deviations. The paper's sufficiently-large-bound convention is represented by interiority of $e^*$; the influence indicator is pinned to the same sign pattern at every feasible profile.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, p. 24, Lemma 7 and equation (14); https://www.anderson.ucla.edu/documents/areas/fac/dotm/bio/pdf_FC16.pdf

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_Setting

namespace CarbonDoubleCount.Planner

variable {ι : Type} {act : ι → Type} {κ : Type}
variable [Fintype ι] [DecidableEq ι]
variable [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
variable [Fintype κ] [DecidableEq κ]

/-- Lemma 7, necessary part: both forms of equation (14). -/
theorem lemma_7_necessary
    (A pS : ℝ) (hA : 0 < A) (hpS : 0 < pS)
    (V : (n : ι) → (act n → ℝ) → ℝ)
    (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (hVdiff : ∀ n, Differentiable ℝ (V n))
    (hfdiff : ∀ i, Differentiable ℝ (fun e => f e i))
    (hVconc : ∀ n, ConcaveOn ℝ (firmBox A n) (V n))
    (hVanti : ∀ n, AntitoneOn (V n) (firmBox A n))
    (hfconv : ∀ i, ConvexOn ℝ (effortBox A) (fun e => f e i))
    (hfanti : ∀ i, AntitoneOn (fun e => f e i) (effortBox A))
    (hfnonneg : ∀ e ∈ effortBox A, ∀ i, 0 ≤ f e i)
    (B : ι → κ → ℝ)
    (hB01 : ∀ n i, B n i = 0 ∨ B n i = 1)
    (hB : ∀ e ∈ effortBox A, ∀ n i,
      (B n i = 1 ↔ (∑ j, dEff (fun e => f e i) e n j) < 0))
    (estar : (n : ι) → act n → ℝ)
    (hfb : IsFirstBest A V f pS estar)
    (hint : ∀ n j, 0 < estar n j ∧ estar n j < A)
    (h : ι → (κ → ℝ) → ℝ)
    (hdiff : ∀ n, Differentiable ℝ (h n))
    (hnash : IsNash A V f h estar) :
    ∀ n j,
      (∑ i, dEff (fun e => f e i) estar n j *
        (dFoot (h n) (f estar) i - pS)) = 0 ∧
      (∑ i, dEff (fun e => f e i) estar n j *
        (dFoot (h n) (f estar) i - pS * B n i)) = 0 := by sorry

end CarbonDoubleCount.Planner
