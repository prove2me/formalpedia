-- Prove2me | Theorems.Thm_CHMSPricing_UnitDemand_revenue_le_copies
-- name    : CHMSPricing.UnitDemand.revenue_le_copies
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:32:47.178768+00:00
-- url     : https://prove2.me/theorems/1b32a905-64b6-4474-8e21-397803c0793b
-- title:
--   Lemma 3, p. 5 — the revenue of a truthful BMUMD mechanism is at most the optimal revenue of the instance with copies
-- statement:
--   Let $\mathcal I$ be an instance of the BMUMD: services $J$ grouped into $J_1,\dots,J_m$, independent values $v_j \sim F_j$, and a unit-demand set system $\mathcal J$. The instance with copies $\mathcal I^{\mathrm{copies}}$ is the single-parameter instance with one agent per service $j \in J$, value $v_j \sim F_j$, and the same set system $\mathcal J$.
--
--   For every individually rational and truthful deterministic mechanism $\mathcal A$ for $\mathcal I$ there is a truthful mechanism $\mathcal A'$ for $\mathcal I^{\mathrm{copies}}$ with
--   $$\mathcal R^{\mathcal A} \le \mathcal R^{\mathcal A'}.$$
--
--   Consequently $\mathcal R^{\mathcal A}$ is at most the optimal revenue of $\mathcal I^{\mathrm{copies}}$, the revenue of Myerson's mechanism there. This is the upper bound through which the multi-parameter problem is compared with a single-parameter one.
--
--   **Formalization Note** The paper's statement bounds $\mathcal R^{\mathcal A}$ by the revenue of Myerson's mechanism for $\mathcal I^{\mathrm{copies}}$. Myerson's mechanism is not constructed in this formalization; the statement asserts the existence of a truthful mechanism for $\mathcal I^{\mathrm{copies}}$ with at least the same revenue, which is what the proof constructs and which gives the paper's statement through the optimality of Myerson's mechanism (Theorem 19, pin P4). The distributions are those of pin P1; no regularity is assumed.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 5, Lemma 3 (proof: p. 13–14, App. B)

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism
import Definitions.Def_CHMSPricing_UnitDemand_MultiMechanism

namespace CHMSPricing.UnitDemand

/-- Lemma 3, p. 5 (existence form, pin P4): for every individually rational, truthful,
deterministic mechanism `𝒜` for an instance `ℐ` of the BMUMD there is a truthful mechanism
for the single-parameter instance with copies `ℐ^copies` (agents `J`, values `v_j ∼ F_j`
independent, the same set system `𝒥`) whose expected revenue is at least `ℛ^𝒜`. -/
theorem revenue_le_copies {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (A : MultiMechanism J m) (hA : IsTruthfulMulti D 𝒥 owner A) :
    ∃ A' : Mechanism J, IsTruthful D 𝒥 A' ∧ revenueMulti D A ≤ revenue D A' := by sorry

end CHMSPricing.UnitDemand
