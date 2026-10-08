-- Prove2me | Theorems.Thm_BoydADMM_Constrained_product_projection
-- name    : BoydADMM.Constrained.product_projection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:07:19.944985+00:00
-- url     : https://prove2.me/theorems/9fabde92-89eb-4706-90dc-825f0dcc986f
-- title:
--   Projection onto a product acts blockwise
-- statement:
--   Let $N\ge1$ and let $\mathcal A_i\subseteq\mathbb R^n$ be nonempty closed convex sets. For block vectors $v=(v_i)$ and $p=(p_i)$, projection onto their Cartesian product is exactly componentwise projection:
--
--   $$p=\Pi_{\mathcal A_1\times\cdots\times\mathcal A_N}(v)\quad\Longleftrightarrow\quad p_i=\Pi_{\mathcal A_i}(v_i)\quad\text{for every }i.$$
--
--   This is the first geometric identity needed to turn product-space ADMM into parallel updates.
--
--   **Formalization Note** The product projection minimizes the sum $\sum_i\|v_i-p_i\|_2^2$, which is the Euclidean metric on the stacked vector. Each component projection uses the published nearest-point predicate.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 35, §5.1.2, product projection display; https://doi.org/10.1561/2200000016

import Mathlib
import Definitions.Def_BoydADMM_Constrained_Geometry

namespace BoydADMM.Constrained

/-- §5.1.2, p. 35: projection onto a Cartesian product acts blockwise. -/
theorem product_projection {N n : ℕ} (hN : 0 < N)
    (A : Fin N → Set (Vec n))
    (hAne : ∀ i, (A i).Nonempty) (hAclosed : ∀ i, IsClosed (A i))
    (hAconvex : ∀ i, Convex ℝ (A i))
    (v p : Blocks N n) :
    IsBlockProjection (productSet A) v p ↔
      ∀ i, RandomGradFree.Nonsmooth.IsMetricProjection (A i) (v i) (p i) := by sorry

end BoydADMM.Constrained
