-- Prove2me | Theorems.Thm_CurbEmissions_ExactStandard_xbar_exists
-- name    : CurbEmissions.ExactStandard.xbar_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:15.944054+00:00
-- url     : https://prove2.me/theorems/68bc1305-9145-4f8d-a198-e0700fe33e8f
-- title:
--   Proof of Lemma A.1, Online Appendix p. 12 (PDF 44) — the equation π1D(s∗1D) = π1U((ū−x)/(c−γ)) has a larger root x̄
-- statement:
--   Let the standing assumptions hold, and let $\pi_{1U}$, $\pi_{1D}$ and $s^*_{1D}$ be as in the model. Then the equation
--   $$\pi_{1D}(s^*_{1D})=\pi_{1U}\Big(\frac{\bar u-x}{c-\gamma}\Big)$$
--   in the unknown $x\in\mathbb R$ has a solution, and its set of solutions has a largest element $\bar x$.
--
--   The constant $\bar x$ enters the third term of condition (1) of Lemma A.1; this result shows that the condition is well defined for every parameter record satisfying the standing assumptions.
-- source:
--   Han, Hu & Dawande, Curbing Emissions: Environmental Regulations and Product Offerings Across Markets, MSOM (authors' accepted manuscript, 2022-07-28), Online Appendix pp. 11–12 (PDF 43–44), proof of Lemma A.1(1)

import Mathlib
import Definitions.Def_CurbEmissions_ExactStandard_Model

namespace CurbEmissions.ExactStandard

/-- Proof of Lemma A.1, Online Appendix p. 12: the equation `π1D(s∗1D) = π1U((ū − x)/(c − γ))` in `x`
has roots, and a largest one `x̄`. -/
theorem xbar_exists (P : Params) (hP : Standing P) :
    ∃ xbar, IsGreatest (xbarEqSet P) xbar := by sorry

end CurbEmissions.ExactStandard
