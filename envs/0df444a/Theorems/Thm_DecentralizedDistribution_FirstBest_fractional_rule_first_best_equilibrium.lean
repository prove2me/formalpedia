-- Prove2me | Theorems.Thm_DecentralizedDistribution_FirstBest_fractional_rule_first_best_equilibrium
-- name    : DecentralizedDistribution.FirstBest.fractional_rule_first_best_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T06:53:46.254328+00:00
-- url     : https://prove2.me/theorems/4583a911-d21f-427a-8c90-695c1c9d438d
-- title:
--   Theorem 5.2 — under the fractional rule AR-f the first-best inventory is a Nash equilibrium
-- statement:
--   Let demand have any probability law $\mu$, and let $\theta_n\in(0,1)$ be constants with $\sum_{n=1}^N\theta_n=1$. Consider the fractional allocation rule AR-f of Eq. (11),
--   $$\alpha^f_n([Z],\vec D)=\theta_n\,P^c_{\mathcal N}([Z],\vec D)-\Big[r_nS_n+v_nH_n-c_nX_n-\sum_{w=1}^W(c_w-v_w)Y_{w,n}\Big].$$
--   If $[Z]^{c*}$ is a first-best profile, i.e. it maximizes the expected centralized profit $J^c_{\mathcal N}$ over all nonnegative profiles, then $[Z]^{c*}$ is a pure-strategy Nash equilibrium (10) of the inventory game under AR-f: no retailer can raise its expected profit by changing its own local stock and claims.
--
--   Under AR-f each retailer's profit is the fixed share $\theta_n$ of the centralized profit, so decentralized stocking reproduces the centrally optimal inventory.
--
--   **Formalization Note.** The paper states the conclusion as "AR-f induces the same equilibrium inventory levels as the first-best"; its proof (p. 367) shows that a first-best profile is an equilibrium, and that direction is what is stated. The converse (every equilibrium is first-best) is not claimed. The paper's weights $\gamma_n$ are written $\theta_n$, and the bracket in (11) carries $+v_nH_n$ (printed as $-v_nH_n$; see the definition file).
-- source:
--   Anupindi, Bassok & Zemel, A General Framework for the Study of Decentralized Distribution Systems, MSOM 3(4) 2001, p. 361, Theorem 5.2, Eq. (11); proof p. 367

import Mathlib
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_Game

open MeasureTheory

namespace DecentralizedDistribution.FirstBest

/-- Theorem 5.2 (p. 361), existence direction. Let `θ_n ∈ (0, 1)` with `∑_n θ_n = 1` (the paper's
`γ_n`). Under the fractional allocation rule AR-f of Eq. (11), every first-best profile
`[Z]^{c*}` (a maximizer of `J^c_𝒩` over nonnegative profiles) is a pure-strategy Nash
equilibrium (10) of the inventory game. -/
theorem fractional_rule_first_best_equilibrium {N W : ℕ} (sys : System N W)
    (μ : Measure (Demand N)) [IsProbabilityMeasure μ]
    (θ : Fin N → ℝ) (hθ : ∀ n, 0 < θ n ∧ θ n < 1) (hθsum : ∑ n, θ n = 1)
    (Zc : Profile N W) (hZc : IsFirstBest sys μ Zc) :
    IsNashEquilibrium sys μ (fractionalRule sys θ) Zc := by sorry

end DecentralizedDistribution.FirstBest
