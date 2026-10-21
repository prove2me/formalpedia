-- Prove2me | Theorems.Thm_FollowCustomers_SmallCost_eq_xii
-- name    : FollowCustomers.SmallCost.eq_xii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:48.039027+00:00
-- url     : https://prove2.me/theorems/912eda80-b9bc-4911-81f1-9d22cd7bd621
-- title:
--   (xii), p. 30 (PDF 32) — log G − 2(G−1)/(G+1) = (3λ/(2δ))·4rK/(p* + p̲)
-- statement:
--   Let $r,\sigma^2,\delta>0$ and $K\in\mathbb R$. Suppose $(\underline x,x^*)$ satisfies equations (x) and (xi), and $p^*+\underline p\neq0$, where $p^*$, $\underline p$ and $G=e^{\lambda(x^*+\underline x-1)}$ are as in the appendix. Then
--   $$(\underline p-p^*)-\frac{4\delta}{3\lambda}\,\frac{G-1}{G+1}=\frac{4rK}{p^*+\underline p}$$
--   and
--   $$\log G-2\,\frac{G-1}{G+1}=\frac{3\lambda}{2\delta}\,\frac{4rK}{p^*+\underline p}.\tag{xii}$$
--
--   Equation (xii) isolates the repositioning cost: its left side vanishes exactly at $G=1$, so as $K\to0$ it forces $G\to1$, which drives both thresholds to $1/2$ and fixes the rate $(G-1)^3\sim 36r\lambda K/\delta$.
--
--   **Formalization Note.** The second identity uses $G=e^{(3\lambda/(2\delta))(\underline p-p^*)}$, so $\log G=\lambda(x^*+\underline x-1)$; the logarithm is taken of a positive number. The hypothesis $p^*+\underline p\neq0$ is the paper's division by $p^*+\underline p$; it holds on every threshold pair, where $p^*>0$ and $\underline p>1$.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), Appendix p. 30 (PDF 32), (xii) and the display before it

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

namespace FollowCustomers.SmallCost

/-- Subtracting (xi) from (x) and dividing by `(1 + G)(p* + p̲)` gives the displayed identity
and (xii) (p. 30). -/
theorem eq_xii (P : Params) (K xl xs : ℝ) (hP : P.Standing)
    (hx : EqX P K xl xs) (hxi : EqXI P K xl xs) (hy : pstar P xs + plow P xl ≠ 0) :
    (plow P xl - pstar P xs) - 4 * P.δ / (3 * lam P) * ((Gf P xl xs - 1) / (Gf P xl xs + 1))
        = 4 * P.r * K / (pstar P xs + plow P xl) ∧
      Real.log (Gf P xl xs) - 2 * (Gf P xl xs - 1) / (Gf P xl xs + 1)
        = 3 * lam P / (2 * P.δ) * (4 * P.r * K / (pstar P xs + plow P xl)) := by sorry

end FollowCustomers.SmallCost
