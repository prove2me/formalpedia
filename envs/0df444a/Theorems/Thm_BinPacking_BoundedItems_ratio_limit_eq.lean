-- Prove2me | Theorems.Thm_BinPacking_BoundedItems_ratio_limit_eq
-- name    : BinPacking.BoundedItems.ratio_limit_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:13:16.627162+00:00
-- url     : https://prove2.me/theorems/e34ef833-4420-4a49-b664-f3004c0617b1
-- title:
--   Corollary of Theorem 2.3 — $\lim_k R^\alpha_{FF}(k)=\lim_k R^\alpha_{BF}(k)=1+\lfloor\alpha^{-1}\rfloor^{-1}$
-- statement:
--   For a real $\alpha$ with $0<\alpha\le\tfrac12$, let $R^\alpha_{FF}(k)$ and $R^\alpha_{BF}(k)$ be the largest values of $FF(L)/L^*$ and $BF(L)/L^*$ over all lists $L$ with every element in $(0,\alpha]$ and optimum $L^*=k$. Then
--   $$\lim_{k\to\infty}R^\alpha_{FF}(k)\;=\;\lim_{k\to\infty}R^\alpha_{BF}(k)\;=\;1+\frac{1}{\lfloor\alpha^{-1}\rfloor}.$$
--
--   For example, if no item exceeds $\tfrac12$ both algorithms are asymptotically within a factor $\tfrac32$ of optimal, and within $\tfrac43$ if no item exceeds $\tfrac13$. The bound interpolates between the unrestricted ratio $\tfrac{17}{10}$ (Section 2 of the paper) and $1$ as the largest item size tends to $0$.
--
--   **Formalization Note** The ratios are suprema in $[0,\infty]$ (`ℝ≥0∞`), so the statement asserts in particular that they are finite for all large $k$. $\lfloor\alpha^{-1}\rfloor$ is `Nat.floor α⁻¹`, cast to `ℝ≥0∞` before inverting; it is at least $2$ under the hypotheses.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 308, Corollary of Theorem 2.3

import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

namespace BinPacking.BoundedItems

open Filter Topology
open scoped ENNReal

/-- Corollary of Theorem 2.3 (Johnson et al. 1974, p. 308): for any positive `α ≤ 1/2`,
`lim_{k→∞} R^α_FF(k) = lim_{k→∞} R^α_BF(k) = 1 + ⌊α⁻¹⌋⁻¹`. -/
theorem ratio_limit_eq (α : ℝ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    Tendsto (ratioFF α) atTop (𝓝 (1 + ((⌊α⁻¹⌋₊ : ℕ) : ℝ≥0∞)⁻¹)) ∧
      Tendsto (ratioBF α) atTop (𝓝 (1 + ((⌊α⁻¹⌋₊ : ℕ) : ℝ≥0∞)⁻¹)) := by sorry

end BinPacking.BoundedItems
