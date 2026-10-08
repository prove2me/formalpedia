-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_optimal_cutoff_rule
-- name    : ForwardRM.Cutoffs.optimal_cutoff_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:59:18.292988+00:00
-- url     : https://prove2.me/theorems/ac4fdbb3-f454-4f44-a7e7-0e449db52fd4
-- title:
--   Theorem 1 — the optimal allocation uses deterministic cutoffs x^k_t, decreasing in k, the unique root of ΔΠ^k_t
-- statement:
--   Let $1\le t\le T$ and $k\ge 1$, and let $x^k_t$ be the cutoff. Then:
--
--   1. $x^k_t\in[\underline v,\bar v]$.
--   2. $x^k_t$ is a deterministic cutoff for period $t$ with $k$ units: for every highest buyer $y^1\in[\underline v,\bar v]$ and every multiset $y^{-1}$ of lower buyers with values in $[\underline v,y^1]$, selling a unit to $y^1$ is optimal in (4.3) when $y^1\ge x^k_t$, and selling nothing is optimal when $y^1\le x^k_t$.
--   3. When $y^1<x^k_t$, selling is not optimal (whatever $y^{-1}$).
--   4. The cutoffs are decreasing in $k$: $x^{k+1}_t\le x^k_t$.
--   5. $x^k_t$ is uniquely determined by
--
--   $$
--   \Delta\Pi^k_t(x^k_t)=0,
--   $$
--
--   that is, $\Delta\Pi^k_t(x^k_t,\varnothing)=0$, and every $y\in[\underline v,\bar v]$ with $\Delta\Pi^k_t(y,\varnothing)=0$ equals $x^k_t$.
--
--   So the seller's optimal decision in each period depends on the number of periods and units left, but not on the number or the values of the other buyers present. This is the paper's first main result; it makes the optimal mechanism implementable without eliciting lower buyers' values.
--
--   **Formalization Note** "Exceeds" is read weakly: at $y^1=x^k_t$ both selling and waiting are optimal. The cutoff is defined as $\inf\{y\in[\underline v,\bar v]:\Delta\Pi^k_t(y,\varnothing)\ge0\}$, from the model alone; that it governs the optimal choice for every $y^{-1}$ is part of the claim.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 15, Theorem 1 (proof p. 16)

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Cutoff

namespace ForwardRM.Cutoffs

/-- Theorem 1 (Board–Skrzypacz, p. 15): with `k ≥ 1` goods in period `t`, the optimal allocation
awards a unit to the highest remaining buyer iff his value is at least the deterministic cutoff
`x^k_t` (whatever the lower buyers' values; at `y¹ = x^k_t` both selling and waiting are optimal),
the cutoffs are decreasing in `k`, and `x^k_t ∈ [v̲, v̄]` is the unique root of `ΔΠ^k_t`. -/
theorem optimal_cutoff_rule (M : Model) (t k : ℕ) (ht : 1 ≤ t) (htT : t ≤ M.T) (hk : 1 ≤ k) :
    M.cutoff t k ∈ Set.Icc M.vlo M.vhi ∧
    M.CutoffRule t k (M.cutoff t k) ∧
    (∀ y1 ∈ Set.Icc M.vlo M.vhi, ∀ S : Multiset ℝ, (∀ s ∈ S, s ∈ Set.Icc M.vlo y1) →
        y1 < M.cutoff t k → ¬ M.SellOptimal t k (y1 ::ₘ S)) ∧
    M.cutoff t (k + 1) ≤ M.cutoff t k ∧
    M.deltaPi t k (M.cutoff t k) 0 = 0 ∧
    (∀ y ∈ Set.Icc M.vlo M.vhi, M.deltaPi t k y 0 = 0 → y = M.cutoff t k) := by sorry

end ForwardRM.Cutoffs
