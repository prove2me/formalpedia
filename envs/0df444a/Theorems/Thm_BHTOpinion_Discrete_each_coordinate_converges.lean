-- Prove2me | Theorems.Thm_BHTOpinion_Discrete_each_coordinate_converges
-- name    : BHTOpinion.Discrete.each_coordinate_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:04.823768+00:00
-- url     : https://prove2.me/theorems/6f4c1d6b-b8f8-4655-b8df-abc9115c6725
-- title:
--   Proof of Theorem 2 — every opinion x_i(t) of a proper solution converges as t → ∞
-- statement:
--   Let $x$ be a proper solution of (2.1). Then every opinion converges: for each agent $i$ there is a real number $x_i^*$ with
--
--   $$\lim_{t\to\infty}x_i(t)=x_i^* .$$
--
--   In the paper this is the step of the proof of Theorem 2 that follows from the monotone, bounded partial sums of (2.3). It is the convergence half of Theorem 2; the other half locates the limit in the equilibrium set $F$.
--
--   **Formalization Note** The paper argues under its convention that the initial condition is sorted; the statement here is for every proper solution, as the paper intends (relabelling the agents preserves properness).
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), proof of Theorem 2, p. 5219

import Mathlib
import Definitions.Def_BHTOpinion_Discrete_Model

open Filter Topology

namespace BHTOpinion.Discrete

theorem each_coordinate_converges {n : ℕ} (x : ℝ → Fin n → ℝ) (hx : IsProperSolution x) :
    ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun t => x t i) atTop (𝓝 L) := by sorry

end BHTOpinion.Discrete
