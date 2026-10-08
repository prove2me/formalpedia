-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_increasing_differences
-- name    : ForwardRM.Cutoffs.increasing_differences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:33:01.966742+00:00
-- url     : https://prove2.me/theorems/bce5b895-8a2d-49cb-bb1e-22671f56dd6a
-- title:
--   (A.1) — Π^k_σ has increasing differences in the number of units and the buyers' values
-- statement:
--   Let $t\ge1$, $k\ge 1$, and suppose that the future cutoffs $\{x^j_s\}_{s\ge t+1}$, $j\le k$, are deterministic and decreasing in $j$. Let $y^1\ge\cdots\ge y^k$ and $\tilde y^1\ge\cdots\ge\tilde y^k$ be values in $[\underline v,\bar v]$ with $y^j\ge\tilde y^j$ for each $j$. Then for every period $\sigma\in\{t+1,\dots,T\}$
--
--   $$
--   \Pi^k_\sigma(y^1,\dots,y^k)-\Pi^k_\sigma(\tilde y^1,\dots,\tilde y^k)\ \ge\ \Pi^{k-1}_\sigma(y^1,\dots,y^k)-\Pi^{k-1}_\sigma(\tilde y^1,\dots,\tilde y^k).
--   $$
--
--   Higher buyer values are worth more to a seller with more units. This increasing-differences property is the step of the proof of Lemma 3(c) that compares sellers with $k$ and $k-1$ units.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 33, Appendix A.1, proof of Lemma 3, Part (c), eq. (A.1)

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction

namespace ForwardRM.Cutoffs

/-- Equation (A.1) (Board–Skrzypacz, Appendix A.1, proof of Lemma 3(c), p. 33): if the future
cutoffs `{x^j_s}_{s ≥ t+1}`, `j ≤ k`, are deterministic and decreasing in `j`, then for ordered
vectors `y¹ ≥ ⋯ ≥ yᵏ` and `ỹ¹ ≥ ⋯ ≥ ỹᵏ` of values in `[v̲, v̄]` with `yʲ ≥ ỹʲ` for each `j`,
and every period `σ ∈ {t+1, …, T}`,
`Π^k_σ(y) − Π^k_σ(ỹ) ≥ Π^{k−1}_σ(y) − Π^{k−1}_σ(ỹ)`. -/
theorem increasing_differences (M : Model) (t k : ℕ) (ht : 1 ≤ t) (hk : 1 ≤ k)
    (hH : M.FutureCutoffsDecreasing t k) (σ : ℕ) (hσ : t + 1 ≤ σ) (hσT : σ ≤ M.T)
    (y y' : Fin k → ℝ) (hy : Antitone y) (hy' : Antitone y') (hle : ∀ i, y' i ≤ y i)
    (hyI : ∀ i, y i ∈ Set.Icc M.vlo M.vhi) (hy'I : ∀ i, y' i ∈ Set.Icc M.vlo M.vhi) :
    M.piVal σ (k - 1) ((List.ofFn y : List ℝ) : Multiset ℝ) -
        M.piVal σ (k - 1) ((List.ofFn y' : List ℝ) : Multiset ℝ) ≤
      M.piVal σ k ((List.ofFn y : List ℝ) : Multiset ℝ) -
        M.piVal σ k ((List.ofFn y' : List ℝ) : Multiset ℝ) := by sorry

end ForwardRM.Cutoffs
