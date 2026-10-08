-- Prove2me | Theorems.Thm_FZEchelon_AverageCost_lemma5_policy_average_cost
-- name    : FZEchelon.AverageCost.lemma5_policy_average_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:43:18.151418+00:00
-- url     : https://prove2.me/theorems/b67852fd-6593-4e5a-a297-f83e2119e292
-- title:
--   Lemma 5, p. 828 — the policy π* has average cost a = a^d + a^r
-- statement:
--   Let $\alpha = 1$, $c^d = c^r = 0$, let $K, h^d, h^r, p^r > 0$, and let the demand be nonnegative, continuous and of finite mean. Let $x^{r*}$ be a global minimizer of $R$. Let $\sigma^d$ be a measurable, nonnegative stationary order rule that is optimal for the depot problem IH$^d$: from every depot state with $\tilde y \ge 0$, its average cost is at most that of every measurable feasible order policy. Let $\pi^*$ order by $\sigma^d$ and ship by the modified critical-number rule with critical number $x^{r*}$. Then for every physical state ($\tilde y \ge 0$, $x^r \le v^d$),
--   $$B(\tilde y, v^d, x^r \mid \pi^*) = a = a^d + a^r,\qquad a^d = B^d(\tilde y, v^d),\ a^r = R(x^{r*}).$$
--
--   Together with the lower bound from value iteration, this gives the optimality of $\pi^*$ (Theorem 2).
--
--   **Formalization Note.** The statement covers every physical state, including $x^r > x^{r*}$, where the paper's proof first waits the finitely many periods until $x^r \le x^{r*}$. The paper takes $\sigma^d$ to be "the policy solving IH$^d$"; its existence (a stationary $(s, S)$ policy) is Iglehart's 1963 result and enters here as the hypothesis on $\sigma^d$, without the $(s, S)$ form. Average costs are $\limsup$s in the extended reals.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 828, Lemma 5; π* defined on p. 825

import Mathlib
import Definitions.Def_FZEchelon_AverageCost_Model
import Definitions.Def_FZEchelon_AverageCost_Policies
import Definitions.Def_FZEchelon_AverageCost_ValueFunctions
open MeasureTheory Filter Topology

namespace FZEchelon.AverageCost

/-- Lemma 5, §3, p. 828: with `α = 1` and `c^d = c^r = 0`, the policy `π*` (orders by an optimal
stationary policy `σd` of the depot problem IH^d, shipments by the modified critical-number rule)
has average cost `a = a^d + a^r`, from every physical state. -/
theorem lemma5_policy_average_cost (m : Model) (hα : m.α = 1) (hcd : m.cd = 0)
    (hcr : m.cr = 0) (hK : 0 < m.K) (hhd : 0 < m.hd) (hhr : 0 < m.hr) (hpr : 0 < m.pr)
    [IsProbabilityMeasure m.ν] (hν0 : m.ν (Set.Iio 0) = 0) (hνatom : ∀ t, m.ν {t} = 0)
    (hνint : Integrable id m.ν)
    (xstar : ℝ) (hx : ∀ x, m.R xstar ≤ m.R x)
    (σd : DepotState m.L → ℝ) (hσm : Measurable σd) (hσ0 : ∀ p, 0 ≤ σd p)
    (hσopt : ∀ p : DepotState m.L, (∀ k, 0 ≤ p.1 k) →
      ∀ π : Policy (DepotState m.L) ℝ, m.DepotAdmissible π p →
        m.depotAvg xstar (m.depotStationary σd) p ≤ m.depotAvg xstar π p) :
    ∀ s : SysState m.L, InDomain s →
      m.sysAvg (m.piStar σd xstar) s
        = m.depotOptAvg xstar (s.1, s.2.1) + ((m.R xstar : ℝ) : EReal) := by sorry

end FZEchelon.AverageCost
