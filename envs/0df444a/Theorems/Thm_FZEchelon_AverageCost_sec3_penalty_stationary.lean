-- Prove2me | Theorems.Thm_FZEchelon_AverageCost_sec3_penalty_stationary
-- name    : FZEchelon.AverageCost.sec3_penalty_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:42:22.774565+00:00
-- url     : https://prove2.me/theorems/cca51385-84d5-40c0-a839-372469762831
-- title:
--   §3, p. 828 — with c^d = c^r = 0, P̂_n = P, ĝ^d_n = g^d_n and ĝ_n = g_n for all n ≥ 1
-- statement:
--   Let $\alpha = 1$, $c^d = c^r = 0$, let $K, h^d, h^r, p^r > 0$, and let the demand be nonnegative, continuous and of finite mean. Let $x^{r*}$ be a global minimizer of $R$, and take $x^{r*}_n = x^{r*}$ for every $n$ as the critical numbers in the induced penalties $\hat P_n$ and the depot program (3). Then for every $n \ge 1$:
--
--   1. $\hat P_n = P$ on the whole real line;
--   2. $\hat g^d_n(\tilde y, v^d) = g^d_n(\tilde y, v^d)$ for all $\tilde y \ge 0$ and $v^d$;
--   3. $\hat g_n(\tilde y, v^d, x^r) = g_n(\tilde y, v^d, x^r) = g^d_n(\tilde y, v^d) + g^r_n(x^r)$ for every physical state ($\tilde y \ge 0$, $x^r \le v^d$).
--
--   Thus in the undiscounted case with free shipments the finite-horizon penalties are already stationary, and the system's value function is the sum of the depot value function with the stationary penalty $P$ and the outlet value function.
--
--   **Formalization Note.** That $x^{r*}$ is a critical number of every period is the preceding §3 claim; here the critical numbers are set to $x^{r*}$ directly. With $\alpha = 1$, $P(x) = R(x) - R(x^{r*})$ for $x < x^{r*}$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 828, §3, first paragraph ('But this result implies that P̂_n = P, so ĝ_n^d = g_n^d and ĝ_n = g_n for all n ≥ 1')

import Mathlib
import Definitions.Def_FZEchelon_AverageCost_Model
import Definitions.Def_FZEchelon_AverageCost_Policies
import Definitions.Def_FZEchelon_AverageCost_ValueFunctions
open MeasureTheory Filter Topology

namespace FZEchelon.AverageCost

/-- §3, p. 828: with `α = 1` and `c^d = c^r = 0`, taking `x_n^{r*} = x^{r*}` for every `n`,
`P̂_n = P`, `ĝ^d_n = g^d_n` and `ĝ_n = g_n` for all `n ≥ 1`. -/
theorem sec3_penalty_stationary (m : Model) (hα : m.α = 1) (hcd : m.cd = 0) (hcr : m.cr = 0)
    (hK : 0 < m.K) (hhd : 0 < m.hd) (hhr : 0 < m.hr) (hpr : 0 < m.pr)
    [IsProbabilityMeasure m.ν] (hν0 : m.ν (Set.Iio 0) = 0) (hνatom : ∀ t, m.ν {t} = 0)
    (hνint : Integrable id m.ν)
    (xstar : ℝ) (hx : ∀ x, m.R xstar ≤ m.R x) :
    ∀ n : ℕ, 1 ≤ n →
      m.Phat (fun _ => xstar) n = m.P xstar ∧
      (∀ p : DepotState m.L, (∀ k, 0 ≤ p.1 k) → m.ghatd (fun _ => xstar) n p = m.gd xstar n p) ∧
      ∀ s : SysState m.L, InDomain s → m.ghat n s = m.gsys xstar n s := by sorry

end FZEchelon.AverageCost
