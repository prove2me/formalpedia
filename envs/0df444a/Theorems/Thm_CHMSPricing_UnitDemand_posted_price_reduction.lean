-- Prove2me | Theorems.Thm_CHMSPricing_UnitDemand_posted_price_reduction
-- name    : CHMSPricing.UnitDemand.posted_price_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:55:05.479671+00:00
-- url     : https://prove2.me/theorems/e37e18c8-2014-4345-abee-8835e5fa8306
-- title:
--   Theorem 4, p. 6 — an $\alpha$-approximate OPM for $\mathcal I^{\mathrm{copies}}$ yields a truthful $\alpha$-approximate posted-price mechanism for the BMUMD
-- statement:
--   Let $\mathcal I$ be a BMUMD instance specified by the unit-demand set system $(J, \mathcal J)$, with independent values $v_j \sim F_j$, and let $\mathcal I^{\mathrm{copies}}$ be the corresponding single-parameter instance. Let $\alpha \ge 0$ and let $p$ be prices whose order-oblivious revenue $\alpha$-approximates the optimal revenue of $\mathcal I^{\mathrm{copies}}$:
--   $$\mathcal R^{M'} \le \alpha \cdot \mathcal R^{\mathrm{obl}}_{\mathbf p} \quad\text{for every truthful mechanism } M' \text{ for } \mathcal I^{\mathrm{copies}}.$$
--   Then for every arrival order $\sigma$ of the buyers, the price-menu mechanism $\mathcal P_\sigma$ with prices $p$ is truthful and individually rational for $\mathcal I$, and
--   $$\mathcal R^{\mathcal A} \le \alpha \cdot \mathcal R^{\mathcal P_\sigma}$$
--   for every individually rational, truthful deterministic mechanism $\mathcal A$ for $\mathcal I$.
--
--   This reduces the design of approximately optimal posted-price menus for unit-demand buyers to the design of order-oblivious posted prices in the single-parameter setting.
--
--   **Formalization Note** The paper's statement asserts the existence of "a truthful posted price mechanism"; the formalization names the mechanism of the proof (the price-menu mechanism with the same prices) and asserts the guarantee for every arrival order. "$\alpha$-approximation" presupposes a nonnegative ratio; $\alpha \ge 0$ is stated explicitly. The benchmark is every deterministic truthful individually rational mechanism, which is the paper's "optimal deterministic truthful mechanism".
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 6, Theorem 4 (proof: p. 14, App. B)

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism
import Definitions.Def_CHMSPricing_UnitDemand_MenuMech

namespace CHMSPricing.UnitDemand

/-- Theorem 4, p. 6: if the order-oblivious posted prices `p` `α`-approximate the optimal revenue
for the single-parameter instance `ℐ^copies` (`ℛ^{M'} ≤ α·ℛ^obl_p` for every truthful `M'`),
then for every arrival order `σ` the price-menu mechanism with prices `p` is truthful for the
BMUMD instance `ℐ` and `α`-approximates the revenue of every deterministic truthful
individually rational mechanism for `ℐ`. -/
theorem posted_price_reduction {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (p : J → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hopm : ∀ M' : Mechanism J, IsTruthful D 𝒥 M' → revenue D M' ≤ α * oblRevenue D 𝒥 p) :
    ∀ σ : Equiv.Perm (Fin m),
      IsTruthfulMulti D 𝒥 owner (menuMech 𝒥 owner σ p) ∧
      ∀ A : MultiMechanism J m, IsTruthfulMulti D 𝒥 owner A →
        revenueMulti D A ≤ α * revenueMulti D (menuMech 𝒥 owner σ p) := by sorry

end CHMSPricing.UnitDemand
