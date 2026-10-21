-- Prove2me | Theorems.Thm_FollowCustomers_SmallCost_eq_xx
-- name    : FollowCustomers.SmallCost.eq_xx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:52.551975+00:00
-- url     : https://prove2.me/theorems/ea899ddc-ef41-476c-a2d5-72199d41863f
-- title:
--   (xx), p. 31 (PDF 33) — on every solution branch, (y − 2)/(G − 1)² → −δ²σ²/(54r) as K → 0
-- statement:
--   Let $r,\sigma^2,\delta>0$ and let $K\mapsto(\underline x(K),x^*(K))$ be a solution branch of (14)–(15). With $y(K)=p^*(K)+\underline p(K)$ and $G(K)=e^{\lambda(x^*(K)+\underline x(K)-1)}$,
--   $$\lim_{K\to0^+}\frac{y(K)-2}{(G(K)-1)^2}=-\frac{\delta^2\sigma^2}{54r}.\tag{xx}$$
--
--   Since $x^*-\underline x=3(2-y)/(2\delta)$, this limit, combined with (xix), yields the $K^{2/3}$ rate of the gap between the thresholds.
--
--   **Formalization Note.** The limit is along $K\to0^+$; the branch is only assumed to solve (14)–(15) in the region for small $K$.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), Appendix p. 31 (PDF 33), (xx)

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

namespace FollowCustomers.SmallCost

/-- (xx), p. 31: on every solution branch, `(y − 2)/(G − 1)² → −δ²σ²/(54r)` as `K → 0⁺`. -/
theorem eq_xx (P : Params) (xl xs : ℝ → ℝ) (hP : P.Standing) (hb : IsBranch P xl xs) :
    Tendsto (fun K => (yf P (xl K) (xs K) - 2) / (Gf P (xl K) (xs K) - 1) ^ 2) (𝓝[>] 0)
      (𝓝 (-(P.δ ^ 2 * P.σ2 / (54 * P.r)))) := by sorry

end FollowCustomers.SmallCost
