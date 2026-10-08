-- Prove2me | Theorems.Thm_FZEchelon_AverageCost_sec3_value_iteration_average
-- name    : FZEchelon.AverageCost.sec3_value_iteration_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:42:26.544841+00:00
-- url     : https://prove2.me/theorems/95e82b5e-7207-481e-8bed-d51203177a1e
-- title:
--   §3, p. 828 — ĝ_n(ỹ, v^d, x^r)/n → a = a^d + a^r for every state
-- statement:
--   Let $\alpha = 1$, $c^d = c^r = 0$, let $K, h^d, h^r, p^r > 0$, and let the demand be nonnegative, continuous and of finite mean. Let $x^{r*}$ be a global minimizer of $R$, let $a^d = B^d(\tilde y, v^d)$ be the minimal average cost of the depot problem IH$^d$ (with the stationary penalty $P$), and let $a^r = R(x^{r*})$. Then for every physical state ($\tilde y \ge 0$, $x^r \le v^d$),
--   $$\lim_{n \to \infty} \frac{\hat g_n(\tilde y, v^d, x^r)}{n} = a = a^d + a^r.$$
--
--   Value iteration for the whole system therefore recovers, after division by the horizon, the sum of the depot's and the outlet's minimal average costs. This is the lower-bound half of Theorem 2's proof in value-function form.
--
--   **Formalization Note.** The limit is taken in the extended reals, since $a^d$ is defined there as an infimum over measurable feasible order policies; $a^r = c^r\mu + R(x^{r*})$ reduces to $R(x^{r*})$ because $c^r = 0$. The paper derives this from Iglehart's convergence $g^d_n/n \to a^d$ and property (f).
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 828, §3, display after 'Letting a = a^d + a^r, we have'

import Mathlib
import Definitions.Def_FZEchelon_AverageCost_Model
import Definitions.Def_FZEchelon_AverageCost_Policies
import Definitions.Def_FZEchelon_AverageCost_ValueFunctions
open MeasureTheory Filter Topology

namespace FZEchelon.AverageCost

/-- §3, p. 828: with `α = 1` and `c^d = c^r = 0`, `ĝ_n(ŷ, v^d, x^r)/n → a = a^d + a^r` for every
physical state, where `a^d = B^d(ŷ, v^d)` is the minimal average cost of the depot problem and
`a^r = R(x^{r*})`. -/
theorem sec3_value_iteration_average (m : Model) (hα : m.α = 1) (hcd : m.cd = 0)
    (hcr : m.cr = 0) (hK : 0 < m.K) (hhd : 0 < m.hd) (hhr : 0 < m.hr) (hpr : 0 < m.pr)
    [IsProbabilityMeasure m.ν] (hν0 : m.ν (Set.Iio 0) = 0) (hνatom : ∀ t, m.ν {t} = 0)
    (hνint : Integrable id m.ν)
    (xstar : ℝ) (hx : ∀ x, m.R xstar ≤ m.R x) :
    ∀ s : SysState m.L, InDomain s →
      Tendsto (fun n : ℕ => ((m.ghat n s / n : ℝ) : EReal)) atTop
        (𝓝 (m.depotOptAvg xstar (s.1, s.2.1) + ((m.R xstar : ℝ) : EReal))) := by sorry

end FZEchelon.AverageCost
