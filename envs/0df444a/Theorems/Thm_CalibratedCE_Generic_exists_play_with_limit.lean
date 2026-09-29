-- Prove2me | Theorems.Thm_CalibratedCE_Generic_exists_play_with_limit
-- name    : CalibratedCE.Generic.exists_play_with_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:05:00.472364+00:00
-- url     : https://prove2.me/theorems/f1451594-bd4f-4999-a318-be0bc789e0ff
-- title:
--   Proof of Theorem 2 (p. 47) — a deterministic play sequence whose empirical distribution converges to $D$
-- statement:
--   Let $D$ be a joint distribution over $S(1)\times S(2)$. Then there are sequences $(x_t)_{t\ge 0}$ in $S(1)$ and $(y_t)_{t\ge0}$ in $S(2)$ such that every pair played has positive probability, $D(x_t,y_t) > 0$ for all $t$, and the empirical joint distribution converges to $D$:
--   $$\lim_{t\to\infty} D_t(x,y) = D(x,y)\qquad\text{for all } x\in S(1),\ y\in S(2).$$
--
--   This is the first step of the proof that every correlated equilibrium is a limit of calibrated play: "Let $(x_t, y_t)$ be a deterministic computable sequence such that the limiting joint distribution is $D(x,y)$."
--
--   **Formalization Note** The positivity of $D(x_t,y_t)$ is implicit in the paper; it makes the conditional forecasts of the next step well defined. "Computable" is dropped: the sequences are deterministic by construction and computability plays no role in $\lambda(G)$. $D_t$ uses rounds $0,\dots,t-1$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 47, proof of Theorem (Theorem 2)

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game

open Filter Topology

namespace CalibratedCE.Generic

theorem exists_play_with_limit {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD : IsJointDist D) :
    ∃ (x : ℕ → Fin m) (y : ℕ → Fin n), (∀ t, 0 < D (x t) (y t)) ∧
      ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b)) := by sorry

end CalibratedCE.Generic
