-- Prove2me | Theorems.Thm_AllocationIndices_Precedence_eps_fi_star_near_optimal
-- name    : AllocationIndices.Precedence.eps_fi_star_near_optimal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:18.164005+00:00
-- url     : https://prove2.me/theorems/86ba6782-cb7c-4533-b11a-307a7e8b546c
-- title:
--   Corollary 4.17 — an ε-FI* policy is within $\varepsilon\gamma^{-1}$ of optimal
-- statement:
--   Let $\mathscr F$ be a family of $n$ ordinary jobs on a single machine with precedence constraints (no circuits), no arrivals and no preemption, as in Theorem 4.9: job $i$ yields the reward $V_i e^{-\gamma C_i}$ at its completion time $C_i$, $V_i > 0$, $\gamma > 0$, and the service times $\sigma_i > 0$ are independent. Let $\varepsilon \ge 0$ and let $h$ be an **ε-FI\* policy**: it proceeds in stages, and each stage $(g, \tau)$ it begins satisfies
--   $$\frac{R_{g\tau}(\mathscr G)}{W_{g\tau}(\mathscr G)} \ge \nu(\mathscr G) - \varepsilon,$$
--   where $\mathscr G$ is the family remaining when the stage begins and $\nu(\mathscr G)$ its index (4.15). Then, from every initial set of completed jobs,
--   $$R_h(\mathscr F) \ge R(\mathscr F) - \varepsilon\gamma^{-1},$$
--   where $R_h(\mathscr F) = E\sum_i V_i e^{-\gamma C_i}$ under $h$ and $R(\mathscr F)$ is the supremum of the payoff over all feasible non-preemptive policies.
--
--   The book states the corollary "under the conditions that Theorems 4.9 and 4.10 hold"; this item is the case of Theorem 4.9. At $\varepsilon = 0$ it says that FI\* policies are optimal.
--
--   **Formalization Note** The bound is in the book's continuous-time units: $W_{g\tau} = \gamma^{-1}E(1 - e^{-\gamma\tau})$ and $\gamma^{-1} = \int_0^\infty e^{-\gamma t}\,dt$; no conversion is made. "$R_h(\mathscr F) \ge R(\mathscr F) - \varepsilon\gamma^{-1}$" is stated as $R_g(\mathscr F) - \varepsilon\gamma^{-1} \le R_h(\mathscr F)$ for every feasible policy $g$. The ε-FI\* property is required with probability one over the service times (see the definition).
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.10 p. 112, Corollary 4.17

import Definitions.Def_AllocationIndices_Precedence_Model

open MeasureTheory

namespace AllocationIndices.Precedence

theorem eps_fi_star_near_optimal {n : ℕ} (F : JobFamily n) (A : Finset (Fin n)) (ε : ℝ)
    (hε : 0 ≤ ε) (h : Policy n) (hh : IsEpsFIStarPolicy F A ε h) (g : Policy n)
    (hg : g.Feasible F A) :
    g.payoff F A - ε * F.γ⁻¹ ≤ h.payoff F A := by sorry

end AllocationIndices.Precedence
