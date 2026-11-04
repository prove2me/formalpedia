-- Prove2me | Theorems.Thm_AIMInventory_Known_theorem_6
-- name    : AIMInventory.Known.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:36.779085+00:00
-- url     : https://prove2.me/theorems/88abedf0-4b65-451a-b12a-d04cca528735
-- title:
--   Theorem 6 — non-perishable AIM: if γ ≤ ρ max{b,h}/(hȳ), the excess y_t − ŷ_t is at most the queue Z_t(ρ)
-- statement:
--   Consider the AIM algorithm with non-perishable inventory, cost parameters $h, b > 0$, upper bound $\bar y > 0$, scale $\gamma > 0$ and starting level $\hat y_1 \in [0,\bar y]$, and let $\rho > 0$. If
--   $$\gamma \le \frac{\rho \max\{b,h\}}{h\,\bar y},$$
--   then for every demand path $D_1, D_2, \dots \ge 0$ and every $t \ge 1$,
--   $$y_t - \hat y_t \le Z_t(\rho),$$
--   where $Z_1(\rho) = 0$ and $Z_{t+1}(\rho) = [Z_t(\rho) + \rho/\sqrt t - D_t]^+$.
--
--   The excess of the implemented level over the target is the price of carrying inventory over; this theorem dominates it by the waiting time of a single-server queue whose service times shrink like $\rho/\sqrt t$. It is the paper's link between stochastic gradient descent and queueing.
--
--   **Formalization Note** The paper says "with probability one"; the inequality holds along every demand path and is stated that way. Of Assumption 1, only the constants $\bar y$ and $\rho$ enter: the inequality does not use $y^{NV} \le \bar y$ or $\rho < E[D_1]$, so those are not hypotheses. The paper's proof writes $H_t(y_t)$ for $H_t(\hat y_t)$. $h, b > 0$ and $\bar y > 0$ are implicit in the paper (they appear in denominators).
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 9, Theorem 6

import Mathlib
import Definitions.Def_AIMInventory_Known_AIM
import Definitions.Def_AIMInventory_Known_Queue

namespace AIMInventory.Known

/-- Theorem 6, p. 9: in the non-perishable case, if `γ ≤ ρ max{b, h}/(hȳ)`, then along every
demand path and for every `t ≥ 1` the excess `y_t − ŷ_t` of the AIM run is at most `Z_t(ρ)`. -/
theorem theorem_6 (h b γ ybar ρ yhat1 : ℝ) (hh : 0 < h) (hb : 0 < b) (hγ : 0 < γ)
    (hybar : 0 < ybar) (hρ : 0 < ρ) (hyhat1 : yhat1 ∈ Set.Icc 0 ybar)
    (hγρ : γ ≤ ρ * max b h / (h * ybar))
    (d : CappedBaseStock.DemandPath) (t : ℕ) (ht : 1 ≤ t) :
    aimLevel .nonPerishable ybar γ b h yhat1 d t - aimTarget .nonPerishable ybar γ b h yhat1 d t
      ≤ auxQueue ρ d t := by sorry

end AIMInventory.Known
