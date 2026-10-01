-- Prove2me | Theorems.Thm_BinPacking_BoundedItems_bf_upper_bound
-- name    : BinPacking.BoundedItems.bf_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:12:45.131405+00:00
-- url     : https://prove2.me/theorems/0bf1d0d9-957f-46dc-84e9-5294a87d21c6
-- title:
--   Theorem 2.3(ii), Best-Fit — $BF(L)\le\frac{m+1}{m}L^*+2$ for $L\subseteq(0,\alpha]$
-- statement:
--   Let $0<\alpha\le\tfrac12$ and $m=\lfloor\alpha^{-1}\rfloor$. For every list $L$ all of whose elements lie in $(0,\alpha]$,
--   $$BF(L)\ \le\ \frac{m+1}{m}\,L^*+2,$$
--   where $BF(L)$ is the number of bins used by Best-Fit and $L^*$ the optimal number of unit bins.
--
--   The source states this as part of Theorem 2.3 ("Both (i) and (ii) hold with FF replaced by BF") but gives no proof, saying only that "a similar, but slightly more complicated, argument can be used to prove this for BF". The First-Fit argument does not transfer verbatim, because Best-Fit may place a small item in a later, fuller bin even when an earlier bin has room.
--
--   **Formalization Note** As for the First-Fit version: $m$ is `⌊α⁻¹⌋₊`, the inequality is in `ℝ`.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 307, Theorem 2.3(ii) with FF replaced by BF (no proof given, p. 308)

import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

namespace BinPacking.BoundedItems

/-- Theorem 2.3(ii) (Johnson et al. 1974, p. 307), Best-Fit: for any positive `α ≤ 1/2`,
with `m = ⌊α⁻¹⌋`, every list `L ⊆ (0, α]` satisfies `BF(L) ≤ ((m + 1)/m) L* + 2`.
The paper states this but gives no proof ("a similar, but slightly more complicated,
argument", p. 308). -/
theorem bf_upper_bound (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) (m : ℕ) (hm : m = ⌊α⁻¹⌋₊)
    (L : List ℝ) (hL : IsList L) (hLα : ∀ a ∈ L, a ≤ α) :
    (BF L : ℝ) ≤ ((m : ℝ) + 1) / m * (optBins L : ℝ) + 2 := by sorry

end BinPacking.BoundedItems
