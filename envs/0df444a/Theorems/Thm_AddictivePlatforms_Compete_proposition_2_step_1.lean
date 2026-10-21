-- Prove2me | Theorems.Thm_AddictivePlatforms_Compete_proposition_2_step_1
-- name    : AddictivePlatforms.Compete.proposition_2_step_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:58:23.011993+00:00
-- url     : https://prove2.me/theorems/9b056ba6-e180-4739-917c-7a42f9dde375
-- title:
--   Proof of Proposition 2, Step 1, p. 31 — for K ≥ 2 and Ā > 0 there is a unique d* > 0 satisfying equation (3)
-- statement:
--   Assume Assumptions 1–2 (with the mission's standing pins), let $K \ge 2$ and let the cap satisfy $\overline{A} > 0$. For $d \ge 0$ let $A_K(d) := \arg\max_{A\in[0,\overline{A}]} K u(A/K, d) - C(A)$ be the total attention the consumer spends on $K$ platforms of addictiveness $d$. Then there is exactly one $d^* > 0$ satisfying the indifference condition
--   $$K \cdot u\!\left(\frac{A_K(d^*)}{K}, d^*\right) - C(A_K(d^*)) = (K-1)\cdot u\!\left(\frac{A_{K-1}(d^*)}{K-1}, d^*\right) - C(A_{K-1}(d^*)). \qquad (3)$$
--
--   Equation (3) says the consumer is indifferent between joining all $K$ platforms and dropping one of them; this step constructs the candidate equilibrium addictiveness of Proposition 2.
--
--   **Formalization Note.** Equation (3) at $d$ is stated as: there are maximizers $A_K$ and $A_{K-1}$ over $[0,\overline{A}]$ whose values are equal (so (3) fails if no maximizer exists). For $K = 2$, $A_{K-1} = A_1$ is the capped single-platform choice, not the uncapped $A(d)$. $\overline{A} > 0$ is a disclosed pin: at $\overline{A} = 0$ (3) reads $u(0,d) = 0$, solved by $d = 0$ when $u(0,0) = 0$. The existence pin for $K$ platforms is assumed.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 31, Proof of Proposition 2, Step 1; equation (3), p. 11

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Compete

/-- Proof of Proposition 2, Step 1 (p. 31): for `K ≥ 2` and `Ā > 0` there is a unique `d* > 0`
satisfying equation (3). -/
theorem proposition_2_step_1 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C) (K : ℕ)
    (hK : 2 ≤ K) (hE : UncOptExists u C K) (Abar : ℝ≥0∞) (hAbar : 0 < Abar) :
    ∃! dstar : ℝ, 0 < dstar ∧ Eq3 u C Abar K dstar := by sorry

end AddictivePlatforms.Compete
