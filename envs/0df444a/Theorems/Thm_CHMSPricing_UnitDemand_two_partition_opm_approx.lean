-- Prove2me | Theorems.Thm_CHMSPricing_UnitDemand_two_partition_opm_approx
-- name    : CHMSPricing.UnitDemand.two_partition_opm_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:31:01.840912+00:00
-- url     : https://prove2.me/theorems/72176ae8-2def-4afb-bf7b-31063b83de19
-- title:
--   Theorem 13, p. 9 — for the intersection of two partition matroids some $\mathcal R^{\mathrm{obl}}_{\mathbf p}$ $6.75$-approximates the optimal revenue
-- statement:
--   Let $\mathcal I$ be an instance of the BSMD with independent regular values $v_i \sim F_i$ whose feasibility constraint is the intersection of two partition matroids $\mathcal M_1, \mathcal M_2$. Then there exist prices $p$ such that
--   $$\mathcal R^{M} \le 6.75 \cdot \mathcal R^{\mathrm{obl}}_{\mathbf p}$$
--   for every truthful mechanism $M$ for $\mathcal I$; in particular $\mathcal R^{\mathrm{obl}}_{\mathbf p}$ $6.75$-approximates the revenue $\mathcal R^{\mathcal M}$ of Myerson's mechanism.
--
--   With Theorem 4 this yields the price-menu mechanism of Theorem 14 for unit-demand buyers of several items in several copies, whose constraint is such an intersection.
--
--   **Formalization Note** The comparison is with every truthful mechanism (pin P4), which by Theorem 19 is the paper's comparison with $\mathcal R^{\mathcal M}$; the prices are chosen before the mechanism ($\exists p\ \forall M$). The constant is written $27/4$. Regularity is assumed as in the proof (App. D.4: "the mechanism which achieves a 6.75-approximation when the distributions are regular"); the non-regular extension is out of scope.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 9, Theorem 13 (proof: pp. 19–20, App. D.4)

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism

namespace CHMSPricing.UnitDemand

/-- Theorem 13, p. 9: for an instance of the BSMD (regular distributions) whose feasibility
constraint is the intersection of two partition matroids, there are prices `p` such that
`ℛ^obl_p` `6.75`-approximates the optimal revenue: `ℛ^M ≤ (27/4)·ℛ^obl_p` for every truthful
mechanism `M`. -/
theorem two_partition_opm_approx {ι β₁ β₂ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq β₁] [DecidableEq β₂]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular)
    (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ) :
    ∃ p : ι → ℝ, ∀ M : Mechanism ι,
      IsTruthful D (twoPartitionSystem part₁ cap₁ part₂ cap₂) M →
        revenue D M ≤ (27 / 4 : ℝ) * oblRevenue D (twoPartitionSystem part₁ cap₁ part₂ cap₂) p := by sorry

end CHMSPricing.UnitDemand
