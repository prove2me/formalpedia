-- Prove2me | Theorems.Thm_FollowCustomers_SmallCost_eq_x_xi
-- name    : FollowCustomers.SmallCost.eq_x_xi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:53.582045+00:00
-- url     : https://prove2.me/theorems/fef91839-f3e3-427a-9370-41ab23c29e5f
-- title:
--   (x)–(xi), p. 30 (PDF 32) — (14) and (15) rewritten in the prices p*, p̲ and G
-- statement:
--   Let $r,\sigma^2,\delta>0$, $K\in\mathbb R$, and put $p^*=(3+\delta-2\delta x^*)/3$, $\underline p=(3-\delta+2\delta\underline x)/3$ and $G=e^{\lambda(x^*+\underline x-1)}$. If $(\underline x,x^*)$ satisfies (14), then
--   $$G(\underline p^2-1)-(p^{*2}-1)+\frac{4\delta}{3\lambda}(p^*-G\underline p)+\frac{8\delta^2}{9\lambda^2}(G-1)=2rK(1+G),\tag{x}$$
--   and if it satisfies (15), then
--   $$G(p^{*2}-1)-(\underline p^2-1)+\frac{4\delta}{3\lambda}(Gp^*-\underline p)+\frac{8\delta^2}{9\lambda^2}(G-1)=-2rK(1+G).\tag{xi}$$
--
--   The rewriting uses $\pi_d(x^*)=\tfrac12p^{*2}$, $\pi_d'(x^*)=-\tfrac{2\delta}{3}p^*$, $\pi_d(1-\underline x)=\tfrac12\underline p^2$ and $\pi_d'(1-\underline x)=-\tfrac{2\delta}{3}\underline p$. Equations (x)–(xi) are the polynomial form of the threshold system on which the small-cost analysis operates.
--
--   **Formalization Note.** Only the forward direction is stated: (14) in ratio form forces its denominator to be nonzero, while (x) does not, so the converse fails in a degenerate case.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), Appendix p. 30 (PDF 32), (x)–(xi)

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

namespace FollowCustomers.SmallCost

/-- (14) and (15) rewritten in the prices `p*`, `p̲` and `G` as (x) and (xi) (p. 30). -/
theorem eq_x_xi (P : Params) (K xl xs : ℝ) (hP : P.Standing) :
    (Eq14 P K xl xs → EqX P K xl xs) ∧ (Eq15 P K xl xs → EqXI P K xl xs) := by sorry

end FollowCustomers.SmallCost
