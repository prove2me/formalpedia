-- Prove2me | Theorems.Thm_CHMSPricing_UnitDemand_optimal_mechanism_exists
-- name    : CHMSPricing.UnitDemand.optimal_mechanism_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:29:33.146653+00:00
-- url     : https://prove2.me/theorems/df2c005e-cf6a-4124-9f93-5fdab9097836
-- title:
--   Theorem 19, p. 12 — a revenue-optimal truthful mechanism exists ($\mathcal R^{\mathcal M} \ge \mathcal R^{\mathcal A}$)
-- statement:
--   Consider a single-parameter instance with independent regular values $v_i \sim F_i$ and a set system $\mathcal J$. There is a truthful mechanism $\mathcal M$ (Myerson's mechanism) such that
--   $$\mathcal R^{\mathcal M} \ge \mathcal R^{\mathcal A} \quad\text{for every truthful mechanism } \mathcal A.$$
--
--   The construction of the prices in Theorem 13 starts from the service probabilities $q^{\mathcal M}_i$ of this optimal mechanism, so its existence is what allows one set of prices to serve as a benchmark for all truthful mechanisms at once.
--
--   **Formalization Note** The statement is the existence content of Theorem 19: Myerson's mechanism is not constructed (pin P4). It is stated for regular distributions, the case used by the body of the paper (pin P2); the paper's theorem also covers non-regular distributions through ironing.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 12, Theorem 19, App. A

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism

namespace CHMSPricing.UnitDemand

/-- Theorem 19, p. 12 (existence form, pin P4): with regular distributions there is a truthful
mechanism (Myerson's) whose expected revenue `ℛ^ℳ` is at least `ℛ^𝒜` for every truthful
mechanism `𝒜`. -/
theorem optimal_mechanism_exists {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular) (𝒥 : SetSystem ι) :
    ∃ Mstar : Mechanism ι, IsTruthful D 𝒥 Mstar ∧
      ∀ A : Mechanism ι, IsTruthful D 𝒥 A → revenue D A ≤ revenue D Mstar := by sorry

end CHMSPricing.UnitDemand
