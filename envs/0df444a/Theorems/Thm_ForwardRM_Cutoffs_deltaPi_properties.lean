-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_deltaPi_properties
-- name    : ForwardRM.Cutoffs.deltaPi_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:59:09.711257+00:00
-- url     : https://prove2.me/theorems/a4dcc660-92d3-4605-9485-ff23ac4636c7
-- title:
--   Lemma 3 — ΔΠ is independent of y⁻¹, continuous and strictly increasing in y¹, and increasing in k
-- statement:
--   Let $1\le t\le T$ and $k\ge1$, and suppose that the future cutoffs $\{x^j_s\}_{s\ge t+1}$ are deterministic and decreasing in $j\le k$. Then:
--
--   1. $\Delta\Pi^k_t(y^1,y^{-1})$ is independent of $y^{-1}$: for every $y^1\in[\underline v,\bar v]$ and every multiset of lower buyers with values in $[\underline v,y^1]$, $\Delta\Pi^k_t(y^1,y^{-1})=\Delta\Pi^k_t(y^1,\varnothing)$; write $\Delta\Pi^k_t(y^1)$ for this common value.
--   2. $\Delta\Pi^k_t(y^1)$ is continuous and strictly increasing in $y^1$ on $[\underline v,\bar v]$.
--   3. $\Delta\Pi^k_t(y^1)$ is increasing in $k$: if $k\ge 2$, then for every $y^1\in[\underline v,\bar v]$
--
--   $$
--   \Delta\Pi^{k-1}_t(y^1)\le\Delta\Pi^k_t(y^1).
--   $$
--
--   These are the three properties that make the cutoff of Theorem 1 deterministic, unique, and decreasing in the number of units.
--
--   **Formalization Note** The hypothesis is the backward-induction hypothesis of the paper and is kept as stated: the lemma is only claimed under it.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 15, Lemma 3 (proof in Appendix A.1, pp. 33–34)

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Cutoff

namespace ForwardRM.Cutoffs

/-- Lemma 3 (Board–Skrzypacz, p. 15): suppose the future cutoffs `{x^j_s}_{s ≥ t+1}` are
deterministic and decreasing in `j ≤ k`. Then
(a) `ΔΠ^k_t(y¹, y^{-1})` does not depend on the lower buyers `y^{-1}`;
(b) `ΔΠ^k_t(y¹)` is continuous and strictly increasing in `y¹` on `[v̲, v̄]`;
(c) `ΔΠ^k_t(y¹)` is (weakly) increasing in `k`. -/
theorem deltaPi_properties (M : Model) (t k : ℕ) (ht : 1 ≤ t) (htT : t ≤ M.T) (hk : 1 ≤ k)
    (hH : M.FutureCutoffsDecreasing t k) :
    (∀ y1 ∈ Set.Icc M.vlo M.vhi, ∀ S : Multiset ℝ, (∀ s ∈ S, s ∈ Set.Icc M.vlo y1) →
        M.deltaPi t k y1 S = M.deltaPi t k y1 0) ∧
    (ContinuousOn (fun y => M.deltaPi t k y 0) (Set.Icc M.vlo M.vhi) ∧
        StrictMonoOn (fun y => M.deltaPi t k y 0) (Set.Icc M.vlo M.vhi)) ∧
    (2 ≤ k → ∀ y1 ∈ Set.Icc M.vlo M.vhi, M.deltaPi t (k - 1) y1 0 ≤ M.deltaPi t k y1 0) := by sorry

end ForwardRM.Cutoffs
