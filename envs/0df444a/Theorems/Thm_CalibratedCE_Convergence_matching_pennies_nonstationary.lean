-- Prove2me | Theorems.Thm_CalibratedCE_Convergence_matching_pennies_nonstationary
-- name    : CalibratedCE.Convergence.matching_pennies_nonstationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:34:10.124306+00:00
-- url     : https://prove2.me/theorems/366f2d22-c86d-45a1-8902-aafab601f105
-- title:
--   Matching pennies (p. 46): with a non-stationary tie-break, calibrated best responses need not converge to a CE
-- statement:
--   Consider matching pennies, $u_1(a, b) = 1$ if $a = b$ and $-1$ otherwise, $u_2 = -u_1$, with heads $= 0$ and tails $= 1$. In every round both players forecast $(1/2, 1/2)$, and both play tails in odd rounds and heads in even rounds, so the plays are Tt, Hh, Tt, Hh, …. Let $D_t$ be the empirical joint distribution of these plays. Then:
--
--   1. the forecast $(1/2, 1/2)$ is a probability vector;
--   2. every play of the row player is a best response to its forecast, and so is every play of the column player (there is a tie);
--   3. no stationary rule produces these plays: there is no function $R$ with $x(s) = R(f(s))$ for all $s$;
--   4. each player's forecast is calibrated against the other's plays;
--   5. yet $D_t$ does not approach the set of correlated equilibria:
--   $$\neg\Big(\forall \varepsilon > 0\ \exists T\ \forall t \ge T\ \exists D \in \pi(G):\ \max_{a,b} |D_t(a, b) - D(a, b)| \le \varepsilon\Big).$$
--
--   The paper's text (p. 46): "Clearly the forecasts of each player are calibrated, but the distribution of plays does not converge to a CE." The example shows that the stationarity assumption in Theorem 1 cannot be dropped.
--
--   **Formalization Note** Both players use the same forecast and the same play sequence, so one calibration clause covers both players. Item 5 is the exact negation of the conclusion of Theorem 1 as formalized. Round $s+1$ of the paper is index $s$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 46 (matching pennies with a non-stationary tie-breaking rule)

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_EmpDist
import Definitions.Def_CalibratedCE_Convergence_MatchingPennies

namespace CalibratedCE.Convergence

/-- Foster–Vohra (1997), p. 46, matching pennies: with the constant forecast `(0.5, 0.5)` and the
non-stationary tie-break "heads on even rounds, tails on odd rounds", every play is a best reply
to its forecast, the plays cannot come from any stationary rule applied to the forecasts, both
forecasts are calibrated, and yet the empirical joint distribution does not converge to the set
of correlated equilibria. -/
theorem matching_pennies_nonstationary :
    (∀ s, IsDist (mpForecast s)) ∧
    (∀ s, ∀ a' : Fin 2,
      ∑ b, mpForecast s b * mpU₁ a' b ≤ ∑ b, mpForecast s b * mpU₁ (mpPlay s) b) ∧
    (∀ s, ∀ b' : Fin 2,
      ∑ a, mpForecast s a * mpU₂ a b' ≤ ∑ a, mpForecast s a * mpU₂ a (mpPlay s)) ∧
    (¬ ∃ R : (Fin 2 → ℝ) → Fin 2, ∀ s, mpPlay s = R (mpForecast s)) ∧
    Shared.Calibrated mpForecast mpPlay ∧
    ¬ (∀ ε > 0, ∃ T : ℕ, ∀ t ≥ T, ∃ D : Fin 2 → Fin 2 → ℝ, IsCE mpU₁ mpU₂ D ∧
      ∀ a b, |empDist mpPlay mpPlay t a b - D a b| ≤ ε) := by sorry

end CalibratedCE.Convergence
