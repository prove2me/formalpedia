-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_sell_monotone_in_value
-- name    : ForwardRM.Cutoffs.sell_monotone_in_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:32:35.284989+00:00
-- url     : https://prove2.me/theorems/80c2909f-7e77-4474-a05c-7539a79de9de
-- title:
--   Lemma 1 — the optimal allocation is monotone in the value of the buyer in line
-- statement:
--   Consider period $t\in\{1,\dots,T\}$, a seller with $k\ge1$ units, a highest buyer with value $y^1\in[\underline v,\bar v]$ and lower buyers $y^{-1}$ with values in $[\underline v,y^1]$. Suppose that selling at least one unit (hence one to $y^1$) is optimal in the Bellman equation (4.3). If the highest buyer's value is raised to $\hat y^1\in(y^1,\bar v]$, the lower buyers unchanged, then selling is still optimal and selling nothing is strictly suboptimal:
--
--   $$
--   \text{sell optimal at }(y^1,y^{-1}),\ y^1<\hat y^1\ \Longrightarrow\ \text{sell optimal and wait not optimal at }(\hat y^1,y^{-1}).
--   $$
--
--   Since the state after $k-j$ sales within a period is again of this form (with $j$ units), the lemma says that the allocation of every unit is monotone in the value of the buyer whose turn it is, so the optimal mechanism is described by cutoffs $x^j_t(y^{-(k-j+1)})$.
--
--   **Formalization Note** "Optimal" refers to the maximum in (4.3) over every number of units sold today.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 13, Lemma 1 (proof p. 14)

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction

namespace ForwardRM.Cutoffs

/-- Lemma 1 (Board–Skrzypacz, p. 13): the allocation is monotone in the value of the buyer
whose turn it is. If, in period `t` with `k` units, selling (at least) the unit to the highest buyer
`y¹` is optimal, then for any higher value `ŷ¹ > y¹` (the lower buyers unchanged) selling is still
optimal and waiting is strictly worse; hence the allocation is described by a cutoff. -/
theorem sell_monotone_in_value (M : Model) (t k : ℕ) (ht : 1 ≤ t) (htT : t ≤ M.T) (hk : 1 ≤ k)
    (y1 y1' : ℝ) (hy1 : y1 ∈ Set.Icc M.vlo M.vhi) (hy1' : y1' ∈ Set.Icc M.vlo M.vhi)
    (hlt : y1 < y1') (S : Multiset ℝ) (hS : ∀ s ∈ S, s ∈ Set.Icc M.vlo y1)
    (hsell : M.SellOptimal t k (y1 ::ₘ S)) :
    M.SellOptimal t k (y1' ::ₘ S) ∧ ¬ M.WaitOptimal t k (y1' ::ₘ S) := by sorry

end ForwardRM.Cutoffs
