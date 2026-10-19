-- Prove2me | Theorems.Thm_CrossLicensing_Innovation_khat2_decreasing
-- name    : CrossLicensing.Innovation.khat2_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T13:01:31.094994+00:00
-- url     : https://prove2.me/theorems/ac355e10-7d6a-4651-bab7-68cddaa493a3
-- title:
--   Proof of Proposition 2, p. A.2 — k̂2(k1|β) is strictly decreasing in β on [0, 1] with k̂2(k1|1) = 0
-- statement:
--   Let $k_1 > 49/144$ and
--   $$\hat k_2(k_1\mid\beta) = -\frac{(4\sqrt3-5)(\beta-1)(5\beta-7)k_1}{(4\sqrt3-7)(\beta-1)(5\beta-7) + 48(3-2\sqrt3)k_1}.$$
--   Then $\beta \mapsto \hat k_2(k_1\mid\beta)$ is strictly decreasing on $[0, 1]$, and $\hat k_2(k_1\mid 1) = 0$.
--
--   Consequently the boundary duopoly region $49/144 < k_2 < \hat k_2(k_1\mid\beta)$ shrinks as $\beta$ increases and is empty for $\beta$ large enough: the paper's "This region shrinks to empty as $\beta$ increases".
--
--   **Formalization Note** The paper states $\partial\hat k_2/\partial\beta < 0$; the formal statement records the consequence used, strict decrease on $[0, 1]$.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), proof of Proposition 2, p. A.2 (PDF 34)

import Mathlib
import Definitions.Def_CrossLicensing_Innovation_ClosedForms

namespace CrossLicensing.Innovation

theorem khat2_decreasing (k1 : ℝ) (hk1 : 49 / 144 < k1) :
    StrictAntiOn (fun β => khat2 β k1) (Set.Icc 0 1) ∧ khat2 1 k1 = 0 := by sorry

end CrossLicensing.Innovation
