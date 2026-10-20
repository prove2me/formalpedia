-- Prove2me | Theorems.Thm_BundleSearch_MatureNew_proposition_2_i
-- name    : BundleSearch.MatureNew.proposition_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:26:12.269993+00:00
-- url     : https://prove2.me/theorems/2ef98a8d-799c-42ec-a8fa-ed1320c35cb0
-- title:
--   Proposition 2, first case, p. 13 — low-cost optimal bundle
-- statement:
--   For $0\le c\le2-3\sqrt7/4$, the bundle price below maximizes revenue over every nonnegative bundle price:
--
--   $$p_B^*=\frac{\sqrt{6(1+c)}}{3},\qquad R_B(c,p_B^*)=\frac29(1+c)\sqrt{6(1+c)}.$$
--
--   The revenue is the greatest value of the bundle-revenue function built from the customers' search and purchase decisions. This is the first case of Proposition 2, with no uniqueness claim.
-- source:
--   Wu, Jin & Chen, Managing Customer Search via Product Bundling, SSRN working paper 3692871 (version of 2022-01-17), p. 13, Proposition 2, case 0 ≤ c ≤ 2 − 3√7/4

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Model

namespace BundleSearch.MatureNew

/-- Proposition 2, first case, p. 13: the low-cost optimal bundle price and revenue. -/
theorem proposition_2_i (c : ℝ) (hc : 0 ≤ c)
    (hc' : c ≤ 2 - 3 * Real.sqrt 7 / 4) :
    IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ))
      (2 / 9 * (1 + c) * Real.sqrt (6 * (1 + c))) ∧
    bundleRevenue c (Real.sqrt (6 * (1 + c)) / 3) =
      2 / 9 * (1 + c) * Real.sqrt (6 * (1 + c)) := by sorry

end BundleSearch.MatureNew
