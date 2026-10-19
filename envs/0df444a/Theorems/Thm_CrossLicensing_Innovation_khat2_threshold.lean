-- Prove2me | Theorems.Thm_CrossLicensing_Innovation_khat2_threshold
-- name    : CrossLicensing.Innovation.khat2_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T13:01:32.336877+00:00
-- url     : https://prove2.me/theorems/affea855-7749-4bcb-a5bc-a1fc69a13d87
-- title:
--   Proof of Proposition 2, p. A.2 — at k2 = k̂2(k1|β) the candidates meet, T^I_2 = T^B_2; for k2 ≥ k̂2 the interior candidate is in the duopoly region
-- statement:
--   Assume $0 \le \beta \le 1$, $49/144 < k_2 < k_1$ and $\beta < \sqrt3 - 1$. Then, with $T^I_i$, $T^B_2$, $\hat T_2$ and
--   $$\hat k_2(k_1\mid\beta) = -\frac{(4\sqrt3-5)(\beta-1)(5\beta-7)k_1}{(4\sqrt3-7)(\beta-1)(5\beta-7) + 48(3-2\sqrt3)k_1}$$
--   as printed in the paper:
--
--   1. if $k_2 = \hat k_2(k_1\mid\beta)$, then $T^I_2 = T^B_2$ ($\hat k_2$ is the solution of $T^I_2 = T^B_2$);
--   2. if $k_2 \ge \hat k_2(k_1\mid\beta)$, then $T^I_2 \le \hat T_2(T^I_1\mid\beta)$, so the interior candidate lies in the region where the supplier induces a duopoly.
--
--   This is the threshold that separates the boundary and the interior duopoly cases of Proposition 2.
--
--   **Formalization Note** The converse of (2) is not posed for all $k_2$: for $k_2$ close to $49/144$ the interior system degenerates.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), proof of Proposition 2, pp. A.1–A.2 (PDF 33–34)

import Mathlib
import Definitions.Def_CrossLicensing_Innovation_Model
import Definitions.Def_CrossLicensing_Innovation_ClosedForms

namespace CrossLicensing.Innovation

theorem khat2_threshold (β k1 k2 : ℝ) (h : Standing β k1 k2) (hβ : β < Real.sqrt 3 - 1) :
    (k2 = khat2 β k1 → TI2 β k1 k2 = TB2 β k1) ∧
    (khat2 β k1 ≤ k2 → TI2 β k1 k2 ≤ That2 β (TI1 β k1 k2)) := by sorry

end CrossLicensing.Innovation
