-- Prove2me | Theorems.Thm_CalibratedCE_Convergence_calibrated_best_response_converges
-- name    : CalibratedCE.Convergence.calibrated_best_response_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:33:39.912867+00:00
-- url     : https://prove2.me/theorems/8a92d3d7-d972-4922-81e5-0e8d94b3a69b
-- title:
--   Theorem 1 — calibrated forecasts with best responses converge to the correlated equilibria
-- statement:
--   Let $G = (u_1, u_2)$ be a finite two-player game with strategy sets $S(1)$, $S(2)$, and let $\pi(G)$ be its set of correlated equilibria. Suppose:
--
--   1. each player selects best responses through a stationary and deterministic rule: $R_1$ maps each probability vector $p$ over $S(2)$ to a best response of player 1 to $p$, and $R_2$ maps each probability vector $q$ over $S(1)$ to a best response of player 2 to $q$;
--   2. in every round $s$, player 1 forecasts player 2's play by a probability vector $f_1(s)$ and player 2 forecasts player 1's play by a probability vector $f_2(s)$;
--   3. the plays are the best responses to the forecasts: $x(s) = R_1(f_1(s))$ and $y(s) = R_2(f_2(s))$;
--   4. each forecast is calibrated against the other player's sequence of plays: $f_1$ with respect to $y$, and $f_2$ with respect to $x$.
--
--   Let $D_t$ be the empirical joint distribution of the first $t$ rounds of play. Then
--   $$\min_{D \in \pi(G)} \ \max_{x \in S(1),\, y \in S(2)} |D_t(x, y) - D(x, y)| \longrightarrow 0 \qquad (t \to \infty).$$
--   Formally: for every $\varepsilon > 0$ there is $T$ such that for every $t \ge T$ some correlated equilibrium $D$ satisfies $|D_t(x, y) - D(x, y)| \le \varepsilon$ for all $x, y$.
--
--   This is the paper's title result: players who best-respond to calibrated forecasts of each other learn, in the limit, a correlated equilibrium of the game, whatever forecasting method they use.
--
--   **Formalization Note** The "min … → 0" is written in its $\varepsilon$-form. The two are equivalent because $\pi(G)$ is nonempty and compact, so the minimum is attained; the $\varepsilon$-form avoids an infimum over a set that Lean would silently evaluate to $0$ if it were empty. The paper's standing assumption (p. 44), "We assume that when players select their best response (for a given forecast) they use a stationary and deterministic tie breaking rule; say the lowest indexed strategy", is the pair of best-reply functions $R_1, R_2$, which depend on the forecast only and not on the round; quantifying over all such functions includes the lowest-index rule. Without stationarity the theorem fails (the matching pennies example of p. 46). Forecasts are given as sequences: the theorem uses only the realized forecasts, and any sequence is produced by a forecasting rule that reads the round number from the history. Rounds are indexed from $0$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 44, Theorem 1 (with the standing assumption of p. 44, Section 3)

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply
import Definitions.Def_CalibratedCE_Convergence_EmpDist

namespace CalibratedCE.Convergence

/-- Foster–Vohra (1997), Theorem 1, p. 44: if each player best-responds, through a stationary
deterministic best-reply function, to a forecast calibrated against the other player's plays,
then the distance from the empirical joint distribution `D_t` to the set of correlated
equilibria, `min_{D ∈ π(G)} max_{x, y} |D_t(x, y) - D(x, y)|`, tends to `0`. -/
theorem calibrated_best_response_converges {m n : ℕ}
    (u₁ u₂ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (hR₁ : IsBestReply₁ u₁ R₁) (hR₂ : IsBestReply₂ u₂ R₂)
    (f₁ : ℕ → Fin n → ℝ) (f₂ : ℕ → Fin m → ℝ)
    (hf₁ : ∀ t, IsDist (f₁ t)) (hf₂ : ∀ t, IsDist (f₂ t))
    (hcal₁ : Shared.Calibrated f₁ (fun s => R₂ (f₂ s)))
    (hcal₂ : Shared.Calibrated f₂ (fun s => R₁ (f₁ s))) :
    ∀ ε > 0, ∃ T : ℕ, ∀ t ≥ T, ∃ D : Fin m → Fin n → ℝ, IsCE u₁ u₂ D ∧
      ∀ a b, |empDist (fun s => R₁ (f₁ s)) (fun s => R₂ (f₂ s)) t a b - D a b| ≤ ε := by sorry

end CalibratedCE.Convergence
