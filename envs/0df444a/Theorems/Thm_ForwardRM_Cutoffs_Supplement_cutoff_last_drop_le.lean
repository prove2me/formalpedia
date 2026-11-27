-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_Supplement_cutoff_last_drop_le
-- name    : ForwardRM.Cutoffs.Supplement.cutoff_last_drop_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:23:35.3983+00:00
-- url     : https://prove2.me/theorems/bab1b930-b323-4e00-b29e-a5ca81dd0288
-- title:
--   Lemma 6 (corrected: adds inf m′ > 0) — with k ≥ 2 units the cutoff falls by at most αh in the last period
-- statement:
--   Consider the continuous-time model with a Lipschitz arrival rate $\lambda$ on $[0,T]$, and assume $\underline m'=\inf_{[\underline v,\bar v]}m'>0$. For $h=T/n$ let $x^k_t$ be the optimal cutoff of the discretized problem at sale date $t$ with $k$ units. Then there are constants $\alpha>0$ and $h_0>0$ such that, for every $h=T/n\le h_0$ with $n\ge2$ and every $k\ge2$,
--
--   $$x^k_{T-h}-x^k_T\le\alpha h .$$
--
--   Together with Lemma 5, this means the cutoffs drop by $O(h)$ per period everywhere except for the last unit at $T$. The final auction of Theorem 3 handles that remaining case.
--
--   **Formalization Note** The sale date $T-h$ is period $n-1$ and $T$ is period $n$ of the discretized model. The requirement $n\ge2$ makes $T-h$ a sale date.
--
--   Differences from the source:
--   - correction: m̲′ = inf m′ > 0 "is strictly positive because m(v) is strictly increasing and continuously differentiable" (p. 36), used through (A.5) → m(y) − m(x) ≥ c(y − x) on [v̲, v̄] for some c > 0 is a hypothesis; reason: strict monotonicity and C¹ do not imply a positive lower slope. The proof explicitly uses this bound in (A.5), p. 36. The printed Lemma 6 is false for a valid density with virtual value m(v) = 16u³ − 32u⁵, u = v − ½, on [0,1], constant λ = 2, r = 1 and k = 2; its last-period cutoff drop is asymptotic to a positive constant times h^{1/3}. DISPROOF.md gives the density and the exact final-period equation. The explicit slope hypothesis restores the domain on which (A.5) and the stated bounds apply. It excludes C¹ strictly increasing marginal revenues with zero one-sided slope somewhere on the support. No separate counterexample to Lemma 5 or Theorem 3 is asserted here.
--   - reading: "for h ≤ h₀" → h = T/n ≤ h₀ with n ≥ 2; reason: T − h must be a sale date h, 2h, …, nh = T (p. 19)
--   - generalization: "there exist positive constants α, h₀" for each k ≥ 2 → one pair (α, h₀) for all k ≥ 2; reason: the constants of the proof, (A.5) and (A.8), do not depend on k, and the uniform statement implies the printed one
--   - reading: Lipschitz continuity of λ, a hypothesis of Theorem 3 → a hypothesis of the lemma; reason: Appendix A.3 proves the lemma under Theorem 3's hypotheses, and its bound λ̄ = max λ comes from them
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 38, Appendix A.3, Lemma 6 (proof p. 38, eq. (A.8))

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Cutoff
import Definitions.Def_ForwardRM_Cutoffs_Supplement_ContinuousModel

namespace ForwardRM.Cutoffs.Supplement

/-- Lemma 6 (Board–Skrzypacz, p. 38). If the arrival rate is Lipschitz on `[0, T]` and
`inf_{[v̲, v̄]} m′ > 0`, there are constants `α > 0` and `h₀ > 0` such that, for every
discretization with `n ≥ 2` periods of length `h = T/n ≤ h₀` and every number of units `k ≥ 2`,
the cutoff falls by at most `αh` in the last period: `x^k_{T−h} − x^k_T ≤ αh`. -/
theorem cutoff_last_drop_le (C : ContinuousModel) (hlip : C.LipschitzRate)
    (hm : C.MarginalRevenueSlopeBounded) :
    ∃ α : ℝ, 0 < α ∧ ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ (n : ℕ) (hn : 1 ≤ n), 2 ≤ n → C.step n ≤ h₀ →
        ∀ k : ℕ, 2 ≤ k →
          (C.discretize n hn).cutoff (n - 1) k - (C.discretize n hn).cutoff n k ≤ α * C.step n := by sorry

end ForwardRM.Cutoffs.Supplement
