-- Prove2me | Theorems.Thm_BinPacking_BoundedItems_lower_bound
-- name    : BinPacking.BoundedItems.lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:10:29.006736+00:00
-- url     : https://prove2.me/theorems/a7ec3e1f-596d-405a-986b-61294b2e30a0
-- title:
--   Theorem 2.3(i) — lists $L\subseteq(0,\alpha]$ with $L^*=k$ and $FF(L),\,BF(L)\ge\frac{m+1}{m}L^*-\frac1m$
-- statement:
--   Let $0<\alpha\le\tfrac12$ and $m=\lfloor\alpha^{-1}\rfloor$. For every integer $k\ge 1$:
--
--   1. there is a list $L$ with every element in $(0,\alpha]$ and $L^*=k$ such that
--   $$FF(L)\ \ge\ \frac{m+1}{m}\,L^*-\frac1m;$$
--   2. there is a list $L$ with every element in $(0,\alpha]$ and $L^*=k$ such that
--   $$BF(L)\ \ge\ \frac{m+1}{m}\,L^*-\frac1m.$$
--
--   Here $L^*$ is the optimal number of unit bins and $FF(L)$, $BF(L)$ are the numbers of bins used by First-Fit and Best-Fit. This is the lower-bound half of Theorem 2.3: it shows that the ratio $\frac{m+1}{m}$ in the upper bound of Theorem 2.3(ii) cannot be improved, for every value of $L^*$.
--
--   **Formalization Note** $m$ is `⌊α⁻¹⌋₊` (`Nat.floor`), passed as a variable with the hypothesis `m = ⌊α⁻¹⌋₊`; under $0<\alpha\le\frac12$ it is at least $2$. The fractions are computed in `ℝ` after casting $m$. The two parts are stated with separate lists, exactly as "Both (i) and (ii) hold with FF replaced by BF"; the paper's construction happens to give one list serving both.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 307, Theorem 2.3(i) (with FF replaced by BF); construction pp. 307-308

import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

namespace BinPacking.BoundedItems

/-- Theorem 2.3(i) (Johnson et al. 1974, p. 307), for First-Fit and for Best-Fit: for any
positive `α ≤ 1/2`, with `m = ⌊α⁻¹⌋`, for each `k ≥ 1` there is a list `L ⊆ (0, α]` with
`L* = k` and `FF(L) ≥ ((m + 1)/m) L* − 1/m`; and likewise with `FF` replaced by `BF`. -/
theorem lower_bound (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) (m : ℕ) (hm : m = ⌊α⁻¹⌋₊)
    (k : ℕ) (hk : 1 ≤ k) :
    (∃ L : List ℝ, IsList L ∧ (∀ a ∈ L, a ≤ α) ∧ optBins L = k ∧
        ((m : ℝ) + 1) / m * (optBins L : ℝ) - 1 / m ≤ (FF L : ℝ)) ∧
    (∃ L : List ℝ, IsList L ∧ (∀ a ∈ L, a ≤ α) ∧ optBins L = k ∧
        ((m : ℝ) + 1) / m * (optBins L : ℝ) - 1 / m ≤ (BF L : ℝ)) := by sorry

end BinPacking.BoundedItems
