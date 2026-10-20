-- Prove2me | Theorems.Thm_BundleSearch_MatureNew_mature_optimal
-- name    : BundleSearch.MatureNew.mature_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:26:07.503666+00:00
-- url     : https://prove2.me/theorems/c3e5939f-00de-4f6e-9377-53ad874a57b9
-- title:
--   §4, p. 8 — mature-product price and revenue
-- statement:
--   A mature product's value is known before purchase. Its uniform-valuation revenue at nonnegative price $p$ is $R_M(p)=p\Pr(V_1\ge p)$. The price $1/2$ earns $1/4$, and no admissible price earns more:
--
--   $$R_M(1/2)=1/4,\qquad \forall p\ge0,\ R_M(p)\le1/4.$$
--
--   This supplies the mature-product contribution to the optimal revenue from selling the two products separately.
-- source:
--   Wu, Jin & Chen, Managing Customer Search via Product Bundling, SSRN working paper 3692871 (version of 2022-01-17), p. 8, §4, sentence beginning “A mature product has no valuation uncertainty”

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Model

namespace BundleSearch.MatureNew

/-- §4, p. 8: the optimal price of the mature product is 1/2 and earns 1/4. -/
theorem mature_optimal :
    revenueMature (1 / 2) = 1 / 4 ∧
    ∀ p : ℝ, 0 ≤ p → revenueMature p ≤ 1 / 4 := by sorry

end BundleSearch.MatureNew
