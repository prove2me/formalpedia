-- Prove2me | Theorems.Thm_AddictivePlatforms_Compete_lemma_B_2
-- name    : AddictivePlatforms.Compete.lemma_B_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:58:19.054481+00:00
-- url     : https://prove2.me/theorems/1bdec557-fdcd-4fda-a6fb-b5d4279782bd
-- title:
--   Lemma B.2, p. 28 — for max_{A∈[0,Ā]} y·u(A/y, d) − C(A): A*(y) increasing, A*(y)/y decreasing, V*(y) concave, dV*/dy decreasing in d
-- statement:
--   Assume Assumptions 1–2 (with the mission's standing pins). For $y > 0$ and $d \ge 0$ consider
--   $$\max_{A\in[0,\overline{A}]} \; y\cdot u\!\left(\frac{A}{y}, d\right) - C(A), \qquad (A.1)$$
--   the consumer's problem when she spreads total attention $A$ evenly over "$y$ platforms" of addictiveness $d$. Let $A^*(y,d)$ be a maximizer and $V^*(y,d)$ the maximized value. Then for every $d \ge 0$:
--   1. $A^*(y,d)$ is (weakly) increasing in $y$ on $(0,\infty)$;
--   2. $A^*(y,d)/y$ is (weakly) decreasing in $y$ on $(0,\infty)$;
--   3. $V^*(\cdot,d)$ is concave on $(0,\infty)$;
--
--   and 4. $\partial V^*/\partial y$ is decreasing in $d$, in integrated form: for all $0 < y_1 < y_2$, the map
--   $$d \longmapsto V^*(y_2,d) - V^*(y_1,d)$$
--   is (weakly) decreasing on $[0,\infty)$.
--
--   At $y = K$ the problem defines $A_K(d)$, and $V^*(K,d) - V^*(K-1,d)$ is the consumer's gain from joining the $K$-th platform; the lemma is the engine of Step 1 of Proposition 2.
--
--   **Formalization Note.** The page says "$V^*(y)$ is strictly concave in $y$". That is false: on the paper's Figure 3 instance $u(a,d) = 1 - e^{-(a-d)}$, $C(a) = a/2$ with a large cap, $V^*(y,d) = y\,(1/2 - (d + \ln 2)/2)$ is linear in $y$. The proof shows concavity, which is all that is used downstream, so concavity is stated. The derivative claim is stated as a decreasing difference because the paper does not establish differentiability of $V^*$. The maximizer is a parameter `Astar` assumed to maximize (A.1) for every $y > 0$, $d \ge 0$ (it is unique by strict concavity, and exists when $\overline{A} < \infty$ by compactness).
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 28, Lemma B.2 and (A.1); proof pp. 28–29

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Compete

/-- Lemma B.2 (p. 28). With `A*(y, d)` a maximizer of `y · u(A/y, d) − C(A)` over `A ∈ [0, Ā]` and
`V*(y, d)` the maximized value: `A*` is increasing in `y`, `A*(y)/y` is decreasing in `y`, `V*` is
concave in `y` on `(0, ∞)` (the page says "strictly concave", which is false; see the mission
notes), and `dV*/dy` is decreasing in `d`, stated in integrated form: for `0 < y₁ < y₂`,
`V*(y₂, d) − V*(y₁, d)` is decreasing in `d ≥ 0`. -/
theorem lemma_B_2 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Abar : ℝ≥0∞) (hS : Standing u C)
    (Astar : ℝ → ℝ → ℝ)
    (hA : ∀ y : ℝ, 0 < y → ∀ d : ℝ, 0 ≤ d → IsPerspMax u C Abar y d (Astar y d)) :
    (∀ d : ℝ, 0 ≤ d →
      MonotoneOn (fun y => Astar y d) (Ioi 0) ∧
      AntitoneOn (fun y => Astar y d / y) (Ioi 0) ∧
      ConcaveOn ℝ (Ioi 0) (fun y => perspObj u C y d (Astar y d))) ∧
    ∀ y₁ y₂ : ℝ, 0 < y₁ → y₁ < y₂ →
      AntitoneOn (fun d => perspObj u C y₂ d (Astar y₂ d) - perspObj u C y₁ d (Astar y₁ d))
        (Ici 0) := by sorry

end AddictivePlatforms.Compete
