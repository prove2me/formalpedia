-- Prove2me | Theorems.Thm_CalibratedCE_Convergence_Mb_closed_convex
-- name    : CalibratedCE.Convergence.Mb_closed_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:29:19.75599+00:00
-- url     : https://prove2.me/theorems/a1e5341e-dbf5-4971-a306-dadf2db5fcc0
-- title:
--   Proof of Theorem 1 (p. 45): $M_b(x)$ is closed and convex
-- statement:
--   Let $G = (u_1, u_2)$ be a finite two-player game and $x \in S(1)$. The set $M_b(x)$ of mixtures $p$ over $S(2)$ to which $x$ is a best response of player 1,
--   $$M_b(x) = \Big\{ p \in \Delta(S(2)) : \sum_y p_y\, u_1(x', y) \le \sum_y p_y\, u_1(x, y) \ \text{for all } x' \in S(1) \Big\},$$
--   is a closed and convex subset of $\mathbb{R}^n$. It is contained in the simplex $\Delta(S(2))$ by definition, and it may be empty or have empty interior.
--
--   Closedness lets the proof of Theorem 1 pass to limits inside $M_b(x)$; convexity lets it average forecasts inside $M_b(x)$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 45, proof of Theorem 1

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Convergence_BestReply

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 45: `M_b(x)` is a closed convex subset of the simplex. -/
theorem Mb_closed_convex {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (a : Fin m) :
    IsClosed (Mb u₁ a) ∧ Convex ℝ (Mb u₁ a) := by sorry

end CalibratedCE.Convergence
