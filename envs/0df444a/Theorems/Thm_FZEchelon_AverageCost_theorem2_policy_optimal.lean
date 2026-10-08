-- Prove2me | Theorems.Thm_FZEchelon_AverageCost_theorem2_policy_optimal
-- name    : FZEchelon.AverageCost.theorem2_policy_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:42:41.107272+00:00
-- url     : https://prove2.me/theorems/bcfb1f5a-952b-45ab-9ac4-bfaee2417c40
-- title:
--   Theorem 2, p. 828 — the decomposition policy π* is optimal for the average-cost problem IH
-- statement:
--   Consider the depot–outlet inventory system under the average-expected-cost criterion ($\alpha = 1$), with no proportional order or shipment costs ($c^d = c^r = 0$), positive fixed order cost $K$ and positive holding and penalty rates $h^d, h^r, p^r$, and i.i.d. nonnegative continuous demands with finite mean. Let $x^{r*}$ be a global minimizer of $R$ (the outlet's critical number), and let $\sigma^d$ be a measurable, nonnegative stationary order rule that is optimal for the depot problem IH$^d$ (from every depot state with $\tilde y \ge 0$). Let $\pi^*$ be the stationary policy that orders $\sigma^d(\tilde y, v^d)$ and ships
--   $$z = \max\big(0,\ \min(x^{r*}, v^d + y^L) - x^r\big).$$
--   Then
--
--   1. $\pi^*$ is measurable and feasible from every physical state ($\tilde y \ge 0$, $x^r \le v^d$);
--   2. for every physical state $s$ and every measurable policy $\pi$ feasible from $s$,
--   $$B(s \mid \pi^*) \le B(s \mid \pi),$$
--   where $B(s \mid \pi) = \limsup_{n} \frac1n B_n(s \mid \pi)$ is the average cost.
--
--   That is, $\pi^*$ is optimal for problem IH: the two-echelon average-cost problem is solved by combining an optimal policy of a single-location problem for the depot, with the induced penalty $P$, and the critical-number policy of the outlet.
--
--   **Formalization Note.** The paper reduces to $c^d = c^r = 0$ "without loss of generality", arguing that the average proportional costs are $c^d\mu$ and $c^r\mu$ "under all interesting policies" (p. 827). That class is not specified, and the paper's proofs are written for $c^d = c^r = 0$; the general-cost version is therefore not part of this statement. Policies are deterministic, history-dependent and measurable, and feasibility is required along every demand realization. The existence of $\sigma^d$ (an optimal stationary $(s,S)$ policy) is Iglehart's 1963 result, cited by the paper. Average costs are $\limsup$s in the extended reals.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 828, Theorem 2; problem IH (p. 824), π* (p. 825), reduction to c^d = c^r = 0 (pp. 827-828)

import Mathlib
import Definitions.Def_FZEchelon_AverageCost_Model
import Definitions.Def_FZEchelon_AverageCost_Policies
import Definitions.Def_FZEchelon_AverageCost_ValueFunctions
open MeasureTheory Filter Topology

namespace FZEchelon.AverageCost

/-- Theorem 2, §3, p. 828: the policy `π*` is optimal for problem IH. With `α = 1` and
`c^d = c^r = 0`, `π*` is measurable and feasible from every physical state, and its average cost is
at most that of every measurable feasible policy, from every physical state. -/
theorem theorem2_policy_optimal (m : Model) (hα : m.α = 1) (hcd : m.cd = 0)
    (hcr : m.cr = 0) (hK : 0 < m.K) (hhd : 0 < m.hd) (hhr : 0 < m.hr) (hpr : 0 < m.pr)
    [IsProbabilityMeasure m.ν] (hν0 : m.ν (Set.Iio 0) = 0) (hνatom : ∀ t, m.ν {t} = 0)
    (hνint : Integrable id m.ν)
    (xstar : ℝ) (hx : ∀ x, m.R xstar ≤ m.R x)
    (σd : DepotState m.L → ℝ) (hσm : Measurable σd) (hσ0 : ∀ p, 0 ≤ σd p)
    (hσopt : ∀ p : DepotState m.L, (∀ k, 0 ≤ p.1 k) →
      ∀ π : Policy (DepotState m.L) ℝ, m.DepotAdmissible π p →
        m.depotAvg xstar (m.depotStationary σd) p ≤ m.depotAvg xstar π p) :
    (∀ s : SysState m.L, InDomain s → m.SysAdmissible (m.piStar σd xstar) s) ∧
      ∀ s : SysState m.L, InDomain s →
        ∀ π : Policy (SysState m.L) (ℝ × ℝ), m.SysAdmissible π s →
          m.sysAvg (m.piStar σd xstar) s ≤ m.sysAvg π s := by sorry

end FZEchelon.AverageCost
