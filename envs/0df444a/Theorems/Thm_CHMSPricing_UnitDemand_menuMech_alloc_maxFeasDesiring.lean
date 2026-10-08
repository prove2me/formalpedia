-- Prove2me | Theorems.Thm_CHMSPricing_UnitDemand_menuMech_alloc_maxFeasDesiring
-- name    : CHMSPricing.UnitDemand.menuMech_alloc_maxFeasDesiring
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:54:51.354189+00:00
-- url     : https://prove2.me/theorems/03fa23a8-3bc7-4d21-86bb-50dea7624d3f
-- title:
--   App. B, p. 14 — the price-menu mechanism allocates a maximal feasible set of services
-- statement:
--   Let $\mathcal J$ be a unit-demand set system on the services $J$ of a BMUMD instance. For every arrival order $\sigma$, all prices $p$ and all values $v$, the set $S$ of services allocated by the price-menu mechanism with order $\sigma$ and prices $p$ is a maximal feasible set of desiring services of the instance with copies:
--   1. $S \in \mathcal J$;
--   2. $p_j \le v_j$ for every $j \in S$;
--   3. no service $j \notin S$ with $p_j \le v_j$ has $S \cup \{j\} \in \mathcal J$.
--
--   Hence the revenue of the price-menu mechanism at $v$ is at least $\min_{S \in \mathcal S_v} \sum_{j \in S} p_j$, the integrand of $\mathcal R^{\mathrm{obl}}_{\mathbf p}$, which is how Theorem 4 transfers the guarantee of an order-oblivious pricing of $\mathcal I^{\mathrm{copies}}$ to $\mathcal I$.
--
--   **Formalization Note** The statement holds for every value vector, not only almost surely, and for the fixed tie-breaking rule of the price-menu mechanism.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 14, App. B, proof of Theorem 4

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_MenuMech

namespace CHMSPricing.UnitDemand

/-- App. B, proof of Theorem 4, p. 14: the price-menu mechanism allocates a maximal feasible set
of services; viewed in `ℐ^copies`, its allocation is a maximal feasible set of desiring copies
(`S ∈ 𝒮_v`), for every arrival order, every prices and every value vector. -/
theorem menuMech_alloc_maxFeasDesiring {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (σ : Equiv.Perm (Fin m)) (p v : J → ℝ) :
    IsMaxFeasDesiring 𝒥 p v ((menuMech 𝒥 owner σ p).alloc v) := by sorry

end CHMSPricing.UnitDemand
