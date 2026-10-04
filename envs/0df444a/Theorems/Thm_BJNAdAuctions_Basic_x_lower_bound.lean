-- Prove2me | Theorems.Thm_BJNAdAuctions_Basic_x_lower_bound
-- name    : BJNAdAuctions.Basic.x_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T16:41:24.170987+00:00
-- url     : https://prove2.me/theorems/ec205554-caac-4aad-a9ea-b98f6d3d5c19
-- title:
--   Theorem 1, proof, Inequality (1): exponential lower bound on $x(i)$
-- statement:
--   Let $R > 0$ be such that $b(i,j) \le R\,B(i)$ for all buyers $i$ and products $j$, and run the Allocation Algorithm with $c = (1+R)^{1/R}$ and any tie-breaking rule. Then after each number $k \le m$ of processed products, every buyer $i$ satisfies
--   $$
--   x(i) \;\ge\; \frac{1}{c-1}\left( c^{\,\sum_{j} b(i,j)\,y(i,j)/B(i)} - 1 \right),
--   $$
--   where $x$ and $y$ are the state after the first $k$ products.
--
--   In particular $x(i) \ge 1$ as soon as $\sum_j b(i,j)\,y(i,j) \ge B(i)$, so the algorithm stops allocating to a buyer once its allocated bids reach its budget; this is the heart of Claim (3).
-- source:
--   Buchbinder, Jain & Naor, Online Primal-Dual Algorithms for Maximizing Ad-Auctions Revenue, ESA 2007, DOI 10.1007/978-3-540-75520-3_24, p. 7, Theorem 1, proof, Inequality (1)

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance
import Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm

namespace BJNAdAuctions.Basic

/-- Theorem 1, proof, Inequality (1) (p. 7): if every bid is at most `R` times its buyer's
budget, then after every prefix of the run with `c = (1 + R)^(1/R)`, each buyer's covering
variable satisfies `x(i) ≥ (c^(∑_j b(i, j) y(i, j) / B(i)) - 1)/(c - 1)`. -/
theorem x_lower_bound {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} (inst : Instance I m)
    (R : ℝ) (hR : 0 < R) (hbR : ∀ i j, inst.b i j ≤ R * inst.B i)
    (sel : (I → ℝ) → Fin m → I) (k : ℕ) (hk : k ≤ m) (i : I) :
    1 / ((1 + R) ^ (1 / R) - 1) *
        (((1 + R) ^ (1 / R)) ^ ((∑ j, inst.b i j * (runPrefix inst ((1 + R) ^ (1 / R)) sel k).y i j)
          / inst.B i) - 1)
      ≤ (runPrefix inst ((1 + R) ^ (1 / R)) sel k).x i := by sorry

end BJNAdAuctions.Basic
