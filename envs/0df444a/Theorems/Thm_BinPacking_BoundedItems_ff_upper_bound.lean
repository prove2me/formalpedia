-- Prove2me | Theorems.Thm_BinPacking_BoundedItems_ff_upper_bound
-- name    : BinPacking.BoundedItems.ff_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:12:11.433212+00:00
-- url     : https://prove2.me/theorems/114c8e6c-de23-480d-8b76-5d4d75ca183f
-- title:
--   Theorem 2.3(ii), First-Fit — $FF(L)\le\frac{m+1}{m}L^*+2$ for $L\subseteq(0,\alpha]$
-- statement:
--   Let $0<\alpha\le\tfrac12$ and $m=\lfloor\alpha^{-1}\rfloor$. For every list $L$ all of whose elements lie in $(0,\alpha]$,
--   $$FF(L)\ \le\ \frac{m+1}{m}\,L^*+2,$$
--   where $FF(L)$ is the number of bins used by First-Fit and $L^*$ the optimal number of unit bins.
--
--   Together with Theorem 2.3(i) this pins the asymptotic worst-case ratio of First-Fit on lists with items at most $\alpha$ to $1+\frac1m$.
--
--   **Formalization Note** $m$ is `⌊α⁻¹⌋₊` (`Nat.floor`), introduced through the hypothesis `m = ⌊α⁻¹⌋₊`; the bound is an inequality of reals, with $m$ cast before dividing.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 307, Theorem 2.3(ii); proof p. 308

import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

namespace BinPacking.BoundedItems

/-- Theorem 2.3(ii) (Johnson et al. 1974, p. 307), First-Fit: for any positive `α ≤ 1/2`,
with `m = ⌊α⁻¹⌋`, every list `L ⊆ (0, α]` satisfies `FF(L) ≤ ((m + 1)/m) L* + 2`. -/
theorem ff_upper_bound (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) (m : ℕ) (hm : m = ⌊α⁻¹⌋₊)
    (L : List ℝ) (hL : IsList L) (hLα : ∀ a ∈ L, a ≤ α) :
    (FF L : ℝ) ≤ ((m : ℝ) + 1) / m * (optBins L : ℝ) + 2 := by sorry

end BinPacking.BoundedItems
