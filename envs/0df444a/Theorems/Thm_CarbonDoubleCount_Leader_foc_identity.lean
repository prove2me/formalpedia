-- Prove2me | Theorems.Thm_CarbonDoubleCount_Leader_foc_identity
-- name    : CarbonDoubleCount.Leader.foc_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:25.429398+00:00
-- url     : https://prove2.me/theorems/8bf94e75-96f3-424f-8761-59c2f3770541
-- title:
--   Proof of Proposition 5 (A.4), p. 26 — at e^E, ∂V_n/∂e_{n,j} = p Σ_i b_{n,i} ∂f_i/∂e_{n,j} for every firm n ≠ N
-- statement:
--   Work in the model of §3: firm profits $V_n$ are differentiable, concave and componentwise decreasing on the firm's box; footprints $f_i$ are differentiable, convex, componentwise decreasing and non-negative on the effort box $[0,A]^M$; $b_{n,i}=1$ exactly when $\sum_j \partial f_i/\partial e_{n,j}<0$ (at every profile in the box) and $b_{n,i}=0$ otherwise. Let the carbon leader $N$ pay carbon price $p\ge 0$, let $(g^E,e^E)$ be optimal for $P_E$, and suppose $e^E$ is interior: $0<e^E_{n,j}<A$ for all $n,j$. Then for every firm $n\ne N$ and every action $j$ of firm $n$,
--   $$\frac{\partial V_n(e^E)}{\partial e_{n,j}}=p\sum_{i\in\mathcal I}b_{n,i}\,\frac{\partial f_i(e^E)}{\partial e_{n,j}}.$$
--
--   This first-order identity is what makes rule (12) incentive compatible: under (12) it says that firm $n$'s marginal payoff vanishes at $e^E_n$.
--
--   **Formalization Note.** Partial derivatives are one-variable derivatives along a single coordinate. The page's sentence begins "since f is concave", a slip for the convexity assumed on p. 8; this item does not use either. The reading of $b_{n,i}$ as a sign pattern holding at every profile of the box, and the interiority of $e^E$ (the page's "A is a sufficiently large bound to guarantee interior solutions"), are disclosed hypotheses.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, p. 26, proof of Proposition 5 (App. A.4), "Second, … it is sufficient to verify that ∂V_n(e^E)/∂e_{n,j} = p Σ b_{n,i} ∂f_i(e^E)/∂e_{n,j} …, which must hold from the optimality of e^E in problem P_E …"

import Mathlib
import Definitions.Def_CarbonDoubleCount_Leader_Setting

namespace CarbonDoubleCount.Leader

open Finset

theorem foc_identity
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {act : ι → Type} [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (A p : ℝ) (hA : 0 < A) (hp : 0 ≤ p)
    (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (hVdiff : ∀ n, Differentiable ℝ (V n))
    (hfdiff : ∀ i, Differentiable ℝ (fun e => f e i))
    (hVconc : ∀ n, ConcaveOn ℝ (CarbonDoubleCount.Planner.firmBox A n) (V n))
    (hVanti : ∀ n, AntitoneOn (V n) (CarbonDoubleCount.Planner.firmBox A n))
    (hfconv : ∀ i, ConvexOn ℝ (CarbonDoubleCount.Planner.effortBox A) (fun e => f e i))
    (hfanti : ∀ i, AntitoneOn (fun e => f e i) (CarbonDoubleCount.Planner.effortBox A))
    (hfnonneg : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ i, 0 ≤ f e i)
    (B : ι → κ → ℝ) (hB01 : ∀ n i, B n i = 0 ∨ B n i = 1)
    (hB : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, ∀ n i, (B n i = 1 ↔ ∑ j, dEff (fun e => f e i) e n j < 0))
    (L : ι) (πbar : ι → ℝ)
    (gE : (n : ι) → (act n → ℝ) → ℝ) (eE : (n : ι) → act n → ℝ)
    (hopt : IsOptimalPE A V f p L πbar gE eE)
    (hint : ∀ n j, 0 < eE n j ∧ eE n j < A) :
    ∀ n, n ≠ L → ∀ j : act n,
      dOwn (V n) (eE n) j = p * ∑ i, B n i * dEff (fun e => f e i) eE n j := by sorry

end CarbonDoubleCount.Leader
