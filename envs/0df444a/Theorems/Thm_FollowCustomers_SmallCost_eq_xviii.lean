-- Prove2me | Theorems.Thm_FollowCustomers_SmallCost_eq_xviii
-- name    : FollowCustomers.SmallCost.eq_xviii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:56.329092+00:00
-- url     : https://prove2.me/theorems/e5c2812d-c711-4050-8e2e-1466b776d0fc
-- title:
--   (xviii), p. 31 (PDF 33) — lim_{G→1} (log G − 2(G−1)/(G+1))/(G−1)³ = 1/12
-- statement:
--   The function $h(G)=\log G-2\,\dfrac{G-1}{G+1}$ vanishes to third order at $G=1$:
--   $$\lim_{G\to1}\frac{\log G-2\frac{G-1}{G+1}}{(G-1)^3}=\frac1{12}.\tag{xviii}$$
--
--   Applied to (xii), this limit converts the equation for $G$ into the rate $(G-1)^3/K\to36r\lambda/\delta$, the source of the $K^{1/3}$ scaling of the thresholds.
--
--   **Formalization Note.** The limit is taken along the punctured neighbourhood of $1$ in $\mathbb R$; near $1$ the argument of the logarithm is positive.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), Appendix p. 31 (PDF 33), (xviii)

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

namespace FollowCustomers.SmallCost

/-- (xviii), p. 31: `lim_{G→1} (log G − 2(G − 1)/(G + 1))/(G − 1)³ = 1/12`. -/
theorem eq_xviii :
    Tendsto (fun G : ℝ => (Real.log G - 2 * (G - 1) / (G + 1)) / (G - 1) ^ 3)
      (𝓝[≠] 1) (𝓝 (1 / 12)) := by sorry

end FollowCustomers.SmallCost
