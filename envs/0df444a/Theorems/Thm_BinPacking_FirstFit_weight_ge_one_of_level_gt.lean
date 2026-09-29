-- Prove2me | Theorems.Thm_BinPacking_FirstFit_weight_ge_one_of_level_gt
-- name    : BinPacking.FirstFit.weight_ge_one_of_level_gt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:06:46.057522+00:00
-- url     : https://prove2.me/theorems/e47e202f-48fd-4028-9c5c-dd0256df93c6
-- title:
--   Claim 2.2.3 — a bin of coarseness α < 1/2 and level above 1 − α has weight at least 1
-- statement:
--   Let $L$ be a list of reals in $(0,1]$ and consider the completed First-Fit packing (respectively Best-Fit packing) of $L$. Let a bin of coarseness $\alpha<\tfrac12$ be filled with numbers $b_1\ge b_2\ge\dots\ge b_m$. If
--
--   $$\sum_{i=1}^m b_i>1-\alpha,\qquad\text{then}\qquad\sum_{i=1}^m W(b_i)\ge 1.$$
--
--   The statement consists of the First-Fit and the Best-Fit version. Together with Claim 2.2.4 it shows that all but a bounded number of bins carry weight close to $1$.
--
--   **Formalization Note** The bin is bin number $j$ ($0$-based) of the completed run, with its contents in placement order; the sums do not depend on the order, so the paper's sorted labelling $b_1\ge\dots\ge b_m$ is not needed in the statement.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 305, Claim 2.2.3

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model
import Definitions.Def_BinPacking_FirstFit_W

namespace BinPacking.FirstFit

/-- Claim 2.2.3 (p. 305): in the completed FF packing (resp. BF packing) of `L`, if bin `j` has
coarseness `α < 1/2` and its level exceeds `1 − α`, then the `W`-weights of its items sum to at
least `1`. -/
theorem weight_ge_one_of_level_gt (L : List ℝ) (hL : IsList L) :
    (∀ (j : ℕ) (hj : j < (ffPack L).length), coarseness (ffPack L) j < 1 / 2 →
        1 - coarseness (ffPack L) j < ((ffPack L)[j]).sum →
        1 ≤ (((ffPack L)[j]).map W).sum) ∧
    (∀ (j : ℕ) (hj : j < (bfPack L).length), coarseness (bfPack L) j < 1 / 2 →
        1 - coarseness (bfPack L) j < ((bfPack L)[j]).sum →
        1 ≤ (((bfPack L)[j]).map W).sum) := by sorry

end BinPacking.FirstFit
