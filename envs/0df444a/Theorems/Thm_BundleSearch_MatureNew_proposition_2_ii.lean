-- Prove2me | Theorems.Thm_BundleSearch_MatureNew_proposition_2_ii
-- name    : BundleSearch.MatureNew.proposition_2_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:26:09.628464+00:00
-- url     : https://prove2.me/theorems/c2be66b3-0722-4b65-8cb6-8fb151d2dd50
-- title:
--   Proposition 2, second case, p. 13 — middle-cost optimal bundle
-- statement:
--   For $2-3\sqrt7/4<c\le1/32$, the bundle price below maximizes revenue over every nonnegative bundle price:
--
--   $$p_B^*=1-\sqrt{2c},\qquad R_B(c,p_B^*)=\frac{\sqrt{2c}}2-2c+\frac12.$$
--
--   The statement identifies an attaining price and the greatest revenue in the middle search-cost regime of Proposition 2, without claiming a unique maximizer.
-- source:
--   Wu, Jin & Chen, Managing Customer Search via Product Bundling, SSRN working paper 3692871 (version of 2022-01-17), p. 13, Proposition 2, case 2 − 3√7/4 < c ≤ 1/32

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Model

namespace BundleSearch.MatureNew

/-- Proposition 2, second case, p. 13: the intermediate-cost optimal bundle price and revenue. -/
theorem proposition_2_ii (c : ℝ)
    (hc : 2 - 3 * Real.sqrt 7 / 4 < c) (hc' : c ≤ 1 / 32) :
    IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ))
      (Real.sqrt (2 * c) / 2 - 2 * c + 1 / 2) ∧
    bundleRevenue c (1 - Real.sqrt (2 * c)) =
      Real.sqrt (2 * c) / 2 - 2 * c + 1 / 2 := by sorry

end BundleSearch.MatureNew
