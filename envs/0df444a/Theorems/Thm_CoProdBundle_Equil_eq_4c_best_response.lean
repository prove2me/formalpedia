-- Prove2me | Theorems.Thm_CoProdBundle_Equil_eq_4c_best_response
-- name    : CoProdBundle.Equil.eq_4c_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:37.970339+00:00
-- url     : https://prove2.me/theorems/83420762-1585-41d9-a39c-77670ef0c7fe
-- title:
--   (4a)–(4c), p. 16 — a positive output is a producer's best response iff it solves Q_i = [2 − (bc_iQ/γ)((1/Q^θ)(3/(A−bc)))^{3/2}] Q/(2−3θ)
-- statement:
--   Work under the standing assumptions: $I \ge 1$ producers with costs $0 < c_1 \le \dots \le c_I$, $b > 0$, $A - bw > 0$, $0 < \theta < 2/3$, $0 < \gamma < 1$. Fix nonnegative outputs of all producers, a producer $i$, and a candidate output $x > 0$ for $i$. Let $Q_{-i}$ be the total output of the other producers and $Q = x + Q_{-i}$.
--
--   Then $x$ maximizes producer $i$'s profit $\pi_i = \gamma (Q_i/Q) S(Q) - c_iQ_i$ over all $Q_i \ge 0$ (the others fixed) if and only if
--   $$x = \Bigl[2 - \frac{b c_i Q}{\gamma}\Bigl(\frac{1}{Q^\theta}\,\frac{3}{A-bw}\Bigr)^{3/2}\Bigr]\frac{Q}{2-3\theta}. \qquad (4c)$$
--
--   Equation (4c) is the first-order condition of (4a)–(4b). The statement says that it characterizes a positive best response exactly: every positive best response satisfies it, and every positive solution of it is a best response. Equilibrium outputs are therefore the solutions of the system of these equations, one per active producer.
--
--   **Formalization Note** The paper sets $\partial \pi_i/\partial Q_i = 0$ and does not separately argue that the stationary point is the maximizer; the statement asserts the full characterization. $Q$ depends on $x$, so (4c) is an implicit equation in $x$. Lean's producer `i` is the paper's producer $i+1$; the paper's $c$ in $A - bc$ is `w`.
-- source:
--   Bhargava, Bundling for Flexibility and Variety: An Economic Model for Multiproducer Value Aggregation, author's accepted manuscript (2020; Manag. Sci. doi:10.1287/mnsc.2020.3662), §4.2, (4a)–(4c), p. 16

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

namespace CoProdBundle.Equil

/-- (4a)–(4c), p. 16: a positive output `x` is producer `i`'s best response to the others'
outputs iff it solves (4c) at the aggregate `Q = x + Q_{−i}`. -/
theorem eq_4c_best_response (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (q : Fin I → ℝ) (hq : ∀ j, 0 ≤ q j) (i : Fin I) (x : ℝ) (hx : 0 < x) :
    (∀ y : ℝ, 0 ≤ y →
        payoff γ A b w θ c (Function.update q i y) i ≤ payoff γ A b w θ c (Function.update q i x) i) ↔
      x = br4c γ A b w θ (c i) (x + (total q - q i)) := by sorry

end CoProdBundle.Equil
