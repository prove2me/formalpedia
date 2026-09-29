-- Prove2me | Theorems.Thm_CalibratedCE_Convergence_limit_conditional_mem_Mb
-- name    : CalibratedCE.Convergence.limit_conditional_mem_Mb
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:32:32.298619+00:00
-- url     : https://prove2.me/theorems/d9a24d15-ce3c-42c0-a7d2-60d4a128888f
-- title:
--   Proof of Theorem 1 (p. 45): the limiting conditional distribution given $x$ lies in $M_b(x)$
-- statement:
--   Let $G = (u_1, u_2)$ be a finite two-player game and $R_1$ a best-reply function of player 1. Let player 1 issue forecasts $f(s)$, each a probability vector over $S(2)$, and play $x(s) = R_1(f(s))$; let $y(s)$ be player 2's plays, and suppose $f$ is calibrated with respect to $y$. Let $t_1 < t_2 < \cdots$ be a subsequence along which the empirical joint distributions converge coordinatewise, $D_{t_i}(a, b) \to D(a, b)$. Then for every $a \in S(1)$ with $\sum_c D(a, c) > 0$,
--   $$\Big( \frac{D(a, b)}{\sum_{c \in S(2)} D(a, c)} \Big)_{b \in S(2)} \in M_b(a).$$
--
--   That is, the limiting conditional distribution of player 2's play, given that player 1 plays $a$, is a mixture to which $a$ is a best response. Rows with $\sum_c D(a, c) = 0$ are excluded, as on the page: "If it did, it would mean that the proportion of times that $x$ is played tends to zero. Hence, in the limit, player 1 never plays $x$, so it can be ignored."
--
--   This is player 1's half of the equilibrium property of subsequential limits.
--
--   **Formalization Note** Player 2's plays $y$ are arbitrary here: only player 1's calibration and best responses are used.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 45, proof of Theorem 1

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply
import Definitions.Def_CalibratedCE_Convergence_EmpDist

open Filter Topology

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 45: if player 1 best-responds to forecasts calibrated against player
2's plays `y`, then along any subsequence on which the empirical joint distribution converges
to `D`, every row `a` of `D` with positive mass, normalized, lies in `M_b(a)`. -/
theorem limit_conditional_mem_Mb {m n : ℕ} (u₁ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (hR₁ : IsBestReply₁ u₁ R₁)
    (f₁ : ℕ → Fin n → ℝ) (hf₁ : ∀ s, IsDist (f₁ s)) (y : ℕ → Fin n)
    (hcal : Shared.Calibrated f₁ y) (φ : ℕ → ℕ) (hφ : StrictMono φ) (D : Fin m → Fin n → ℝ)
    (hD : ∀ a b, Tendsto (fun i => empDist (fun s => R₁ (f₁ s)) y (φ i) a b) atTop
      (𝓝 (D a b)))
    (a : Fin m) (ha : 0 < ∑ c, D a c) :
    (fun b => D a b / ∑ c, D a c) ∈ Mb u₁ a := by sorry

end CalibratedCE.Convergence
