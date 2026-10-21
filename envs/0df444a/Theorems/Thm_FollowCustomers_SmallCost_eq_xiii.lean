-- Prove2me | Theorems.Thm_FollowCustomers_SmallCost_eq_xiii
-- name    : FollowCustomers.SmallCost.eq_xiii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:07.406782+00:00
-- url     : https://prove2.me/theorems/ad1d3048-50b6-465c-8a70-1aecbb875c98
-- title:
--   (xiii), p. 30 (PDF 32) — ((G−1)/(p*−p̲))(p̲² + p*² − 2 + 16δ²/(9λ²)) + (4δ/(3λ))(G+1) = 0
-- statement:
--   Let $r,\sigma^2,\delta>0$ and $K\in\mathbb R$. Suppose $(\underline x,x^*)$ satisfies equations (x) and (xi), and $p^*\neq\underline p$. Then
--   $$\frac{G-1}{p^*-\underline p}\Big(\underline p^2+p^{*2}-2+\frac{16\delta^2}{9\lambda^2}\Big)+\frac{4\delta}{3\lambda}(G+1)=0.\tag{xiii}$$
--
--   Equation (xiii) contains no $K$. Together with (xii) it determines the second-order behaviour of $y=p^*+\underline p$, and hence of the gap $x^*-\underline x$, as $K\to0$.
--
--   **Formalization Note.** The hypothesis $p^*\neq\underline p$ is the paper's division by $p^*-\underline p$; on a threshold pair with $K>0$ it holds because (xii) forces $G>1$.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), Appendix p. 30 (PDF 32), (xiii)

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

namespace FollowCustomers.SmallCost

/-- Adding (x) and (xi) and dividing by `p* − p̲` gives (xiii) (p. 30). -/
theorem eq_xiii (P : Params) (K xl xs : ℝ) (hP : P.Standing)
    (hx : EqX P K xl xs) (hxi : EqXI P K xl xs) (hne : pstar P xs ≠ plow P xl) :
    (Gf P xl xs - 1) / (pstar P xs - plow P xl)
        * (plow P xl ^ 2 + pstar P xs ^ 2 - 2 + 16 * P.δ ^ 2 / (9 * lam P ^ 2))
      + 4 * P.δ / (3 * lam P) * (Gf P xl xs + 1) = 0 := by sorry

end FollowCustomers.SmallCost
