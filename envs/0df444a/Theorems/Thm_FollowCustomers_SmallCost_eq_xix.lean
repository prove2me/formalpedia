-- Prove2me | Theorems.Thm_FollowCustomers_SmallCost_eq_xix
-- name    : FollowCustomers.SmallCost.eq_xix
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:55.711432+00:00
-- url     : https://prove2.me/theorems/bae4bc32-447d-41d1-9ddd-d8d41e65b059
-- title:
--   (xix), p. 31 (PDF 33) — on every solution branch, (G − 1)³/K → 36rλ/δ as K → 0
-- statement:
--   Let $r,\sigma^2,\delta>0$, $\lambda=\sqrt{2r/\sigma^2}$, and let $K\mapsto(\underline x(K),x^*(K))$ be a solution branch of (14)–(15). With $G(K)=e^{\lambda(x^*(K)+\underline x(K)-1)}$,
--   $$\lim_{K\to0^+}\frac{(G(K)-1)^3}{K}=\frac{36r\lambda}{\delta}.\tag{xix}$$
--
--   Since $\log G=\lambda(x^*+\underline x-1)$, this gives the leading $K^{1/3}$ behaviour of the sum $x^*+\underline x-1$, and hence of each threshold.
--
--   **Formalization Note.** The limit is along $K\to0^+$; the branch is only assumed to solve (14)–(15) in the region for small $K$.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), Appendix p. 31 (PDF 33), (xix)

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

namespace FollowCustomers.SmallCost

/-- (xix), p. 31: on every solution branch, `(G − 1)³/K → 36rλ/δ` as `K → 0⁺`. -/
theorem eq_xix (P : Params) (xl xs : ℝ → ℝ) (hP : P.Standing) (hb : IsBranch P xl xs) :
    Tendsto (fun K => (Gf P (xl K) (xs K) - 1) ^ 3 / K) (𝓝[>] 0)
      (𝓝 (36 * P.r * lam P / P.δ)) := by sorry

end FollowCustomers.SmallCost
