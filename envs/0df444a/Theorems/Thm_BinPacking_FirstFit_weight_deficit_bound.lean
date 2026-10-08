-- Prove2me | Theorems.Thm_BinPacking_FirstFit_weight_deficit_bound
-- name    : BinPacking.FirstFit.weight_deficit_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:07:17.302852+00:00
-- url     : https://prove2.me/theorems/c2cb84c4-7ee3-4f02-9d8b-8535db4af9b0
-- title:
--   Claim 2.2.4 — a bin with weight deficit β > 0 has level at most 1 − α − (5/9)β
-- statement:
--   Let $L$ be a list of reals in $(0,1]$ and consider the completed First-Fit packing (respectively Best-Fit packing) of $L$. Let a bin of coarseness $\alpha<\tfrac12$ be filled with $b_1\ge\dots\ge b_m$, and suppose
--
--   $$\sum_{i=1}^m W(b_i)=1-\beta\qquad\text{with }\beta>0.$$
--
--   Then either
--
--   1. $m=1$ and $b_1\le\tfrac12$, or
--   2. $\displaystyle\sum_{i=1}^m b_i\le 1-\alpha-\tfrac59\beta$.
--
--   The statement consists of the First-Fit and the Best-Fit version. It converts a weight deficit of a bin into an increase of the coarseness of all later bins, which is what bounds the number of bins of weight less than $1$.
--
--   **Formalization Note** The paper prints alternative (i) as "$m=1$ and $b_1<\tfrac12$". That version is false: First-Fit on the list $(0.6,0.5)$ puts $0.5$ alone in the second bin, whose coarseness is $0.4$ and whose weight is $W(0.5)=0.7$, so $\beta=0.3>0$; neither $b_1<\tfrac12$ nor $0.5\le 1-0.4-\tfrac16$ holds. The paper's proof only excludes $b_1>\tfrac12$ ("If $m=1$ and $b_1>\tfrac12$, it is impossible that $\beta>0$"), and the main proof only uses that such a bin contains no element exceeding $\tfrac12$. The statement here therefore uses $b_1\le\tfrac12$. The bin is bin number $j$ of the completed run; "$m=1$ and $b_1\le\tfrac12$" is written as "the bin is $[b]$ for some $b\le\tfrac12$".
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 306, Claim 2.2.4 (alternative (i) corrected from b₁ < 1/2 to b₁ ≤ 1/2)

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model
import Definitions.Def_BinPacking_FirstFit_W

namespace BinPacking.FirstFit

/-- Claim 2.2.4 (p. 306), with alternative (i) read as `b₁ ≤ 1/2` (the printed `b₁ < 1/2` is a
misprint: FF on `(0.6, 0.5)` is a counterexample): in the completed FF packing (resp. BF
packing) of `L`, if bin `j` has coarseness `α < 1/2` and its `W`-weights sum to `1 − β` with
`β > 0`, then either the bin holds a single item `b₁ ≤ 1/2`, or its level is at most
`1 − α − (5/9)β`. -/
theorem weight_deficit_bound (L : List ℝ) (hL : IsList L) :
    (∀ (j : ℕ) (hj : j < (ffPack L).length) (β : ℝ), coarseness (ffPack L) j < 1 / 2 →
        0 < β → (((ffPack L)[j]).map W).sum = 1 - β →
        (∃ b : ℝ, (ffPack L)[j] = [b] ∧ b ≤ 1 / 2) ∨
          ((ffPack L)[j]).sum ≤ 1 - coarseness (ffPack L) j - 5 / 9 * β) ∧
    (∀ (j : ℕ) (hj : j < (bfPack L).length) (β : ℝ), coarseness (bfPack L) j < 1 / 2 →
        0 < β → (((bfPack L)[j]).map W).sum = 1 - β →
        (∃ b : ℝ, (bfPack L)[j] = [b] ∧ b ≤ 1 / 2) ∨
          ((bfPack L)[j]).sum ≤ 1 - coarseness (bfPack L) j - 5 / 9 * β) := by sorry

end BinPacking.FirstFit
