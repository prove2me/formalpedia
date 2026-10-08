-- Prove2me | Theorems.Thm_BootRobust_NWDual_corollary_1
-- name    : BootRobust.NWDual.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:09.032982+00:00
-- url     : https://prove2.me/theorems/52805834-6468-459f-830f-a2e975aad6e1
-- title:
--   Corollary 1, p. 13 — the robust Nadaraya–Watson budget equals the perspective program over (s, P)
-- statement:
--   Let $R$ be any function assigning an extended real number $R(D',D)$ to pairs of distributions on $\Omega_n$, let $D$ be a reference distribution, $r\in\mathbb R$ a radius, $w_i>0$ positive weights and $\ell_i=L(\bar z,\bar y_i)$ the losses of a fixed decision $\bar z$. Then the robust Nadaraya–Watson budget (24) with $k(n)=n$,
--   $$c_n(\bar z,D,x_0)=\sup\Big\{\frac{\sum_iw_i\ell_iD'_i}{\sum_iw_iD'_i}:\ D'\in\mathcal D_n,\ R(D',D)\le r\Big\},$$
--   equals
--   $$\sup_{s>0,\,P}\ \sum_iw_i\ell_iP_i\quad\text{s.t.}\quad s\,R(P/s,D)\le s\,r,\qquad \sum_iP_i=s,\qquad \sum_iw_iP_i=1,$$
--   where $P/s$ ranges over $\mathcal D_n$. Both sides are extended reals (an empty feasible set gives $-\infty$).
--
--   The reformulation turns a ratio objective into a linear one; when $R$ is convex in its first argument the constraint $s\,R(P/s,D)\le s\,r$ is jointly convex, which is how the paper obtains a convex program.
--
--   **Formalization Note** The statement is the equality of optimal values for an arbitrary $R$; the convexity claimed by the corollary's wording ("can be reformulated as the convex optimization problem") is not part of it. "$P/s\in\mathcal D_n$" is written explicitly because the page's $R$ is defined only on $\mathcal D_n$.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, Corollary 1, p. 13 (proof B.3, p. 27)

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

namespace BootRobust.NWDual

/-- Corollary 1, p. 13: for any distance function `R`, the robust Nadaraya–Watson budget (24)
equals the value of the perspective program over `(s, P)`. -/
theorem corollary_1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : (ι → ℝ) → (ι → ℝ) → EReal) (D : ι → ℝ) (r : ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) {Z : Type*} (L : Z → ι → ℝ) (z : Z) :
    robustNW R D r w (L z) = perspValue R D r w (L z) := by sorry

end BootRobust.NWDual
