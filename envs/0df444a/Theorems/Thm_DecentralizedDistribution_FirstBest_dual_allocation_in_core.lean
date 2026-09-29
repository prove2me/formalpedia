-- Prove2me | Theorems.Thm_DecentralizedDistribution_FirstBest_dual_allocation_in_core
-- name    : DecentralizedDistribution.FirstBest.dual_allocation_in_core
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T06:51:11.672447+00:00
-- url     : https://prove2.me/theorems/cabdeb0c-4866-4ac5-9964-5f969c5aa137
-- title:
--   Theorem 4.1 — the dual-price allocation is in the core of SAG([Z], D)
-- statement:
--   Fix a distribution system, a nonnegative profile $[Z]$ of local stocks and claims (so that all warehouse inventory is claimed) and any demand realization $\vec D$. Consider the snapshot allocation game SAG$([Z],\vec D)$ whose value for a coalition $\mathcal S\subseteq\mathcal N$ is the shipping-LP value $W^*_{\mathcal S}([Z],\vec D)$ of (6). Its core is the set of allocations $\alpha$ with
--   $$\sum_{j\in\mathcal S}\alpha_j\ \ge\ W^*_{\mathcal S}([Z],\vec D)\quad\forall\,\mathcal S\subseteq\mathcal N,\qquad \sum_{j\in\mathcal N}\alpha_j=W^*_{\mathcal N}([Z],\vec D).\qquad(7)$$
--   Then:
--   1. the core of SAG$([Z],\vec D)$ is nonempty;
--   2. the dual of the grand-coalition shipping LP (6) has an optimal solution;
--   3. for every optimal dual solution $(\nu,\gamma,\delta)$, the dual-price allocation
--   $$\alpha_n([Z],\vec D)=\nu_nH_n+\sum_{w\in\mathcal W}\gamma_wY_{w,n}+\delta_nE_n,\qquad n\in\mathcal N,\qquad(8)$$
--   lies in the core.
--
--   This is the paper's main theorem: pricing residual inventory, claimed warehouse stock and residual demand at their shadow prices gives an allocation that no coalition can improve on by shipping among its own members.
--
--   **Formalization Note.** The core is the platform definition `Supermodularity.Cooperative.Core` with ground set all retailers, which is exactly (7a)–(7b) (the empty coalition has value $0$). Part 3 is asserted for every optimal dual, not just one; the paper notes that dual prices need not be unique.
-- source:
--   Anupindi, Bassok & Zemel, A General Framework for the Study of Decentralized Distribution Systems, MSOM 3(4) 2001, p. 358, Theorem 4.1, Eq. (7a)-(7b), (8)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_DualPrices

open Supermodularity.Cooperative

namespace DecentralizedDistribution.FirstBest

/-- Theorem 4.1 (p. 358). For a nonnegative profile `[Z]` (all inventory claimed) and any demand
realization `D⃗`: the core of SAG([Z], D⃗) is nonempty, the dual of the grand-coalition shipping
LP (6) has an optimal solution, and for every optimal dual solution `(ν, γ, δ)` the allocation (8)
`α_n = ν_n H_n + ∑_w γ_w Y_{w,n} + δ_n E_n` lies in the core (7). -/
theorem dual_allocation_in_core {N W : ℕ} (sys : System N W) (Z : Profile N W) (hZ : Z.Nonneg)
    (D : Demand N) :
    (Core Finset.univ (fun S => coalitionValue sys S Z D)).Nonempty ∧
    (∃ p, IsOptimalDual sys Z D p) ∧
    ∀ p, IsOptimalDual sys Z D p →
      dualAllocation Z D p ∈ Core Finset.univ (fun S => coalitionValue sys S Z D) := by sorry

end DecentralizedDistribution.FirstBest
