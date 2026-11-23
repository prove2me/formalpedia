-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_Supplement_cutoff_drop_le
-- name    : ForwardRM.Cutoffs.Supplement.cutoff_drop_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:23:01.022668+00:00
-- url     : https://prove2.me/theorems/aae7d44a-d269-4d9a-98db-ba8ae0d6d68f
-- title:
--   Lemma 5 (corrected: adds inf m′ > 0) — before T − h the optimal cutoffs fall by at most αh per period
-- statement:
--   Consider the continuous-time model with a Lipschitz arrival rate $\lambda$ on $[0,T]$, and assume $\underline m'=\inf_{[\underline v,\bar v]}m'>0$. For $h=T/n$ let $x^k_t$ be the optimal cutoff of the discretized problem at sale date $t=ih$ with $k$ units. Then there are constants $\alpha>0$ and $h_0>0$ such that, for every $h=T/n<h_0$, every $k\ge1$ and every sale date $h\le t\le T-2h$,
--
--   $$x^k_t-x^k_{t+h}\le\alpha h .$$
--
--   The constants do not depend on $h$, $t$ or $k$.
--
--   The lemma says that the cutoffs never jump down by more than $O(h)$ before the last period. The proof of Theorem 3 uses it to bound the probability of two sales in one period by $O(h^2)$.
--
--   **Formalization Note** The sale date $t=ih$ is period $i$ of the discretized model, so the range $h\le t\le T-2h$ is $1\le i\le n-2$. The cutoff is the published `cutoff i k` of the discretized model.
--
--   Differences from the source:
--   - correction: m̲′ = inf m′ > 0 "is strictly positive because m(v) is strictly increasing and continuously differentiable" (p. 36) → m(y) − m(x) ≥ c(y − x) on [v̲, v̄] for some c > 0 is a hypothesis; reason: strict monotonicity and C¹ do not imply a positive lower slope. The proof explicitly uses this bound in (A.5), p. 36. The printed Lemma 6 is false for a valid density with virtual value m(v) = 16u³ − 32u⁵, u = v − ½, on [0,1], constant λ = 2, r = 1 and k = 2; its last-period cutoff drop is asymptotic to a positive constant times h^{1/3}. DISPROOF.md gives the density and the exact final-period equation. The explicit slope hypothesis restores the domain on which (A.5) and the stated bounds apply. It excludes C¹ strictly increasing marginal revenues with zero one-sided slope somewhere on the support. No separate counterexample to Lemma 5 or Theorem 3 is asserted here.
--   - reading: "for t ≤ T − 2h" → sale dates t = ih with 1 ≤ i ≤ n − 2 and h = T/n; reason: sales happen only at h, 2h, …, nh = T (p. 19), and the first sale date is h
--   - generalization: "there exists positive constants α, h₀" for each k → one pair (α, h₀) for all k ≥ 1 and all t; reason: the constants of the proof, (A.5) and (A.7), do not depend on t or k, and the uniform statement implies the printed one
--   - reading: Lipschitz continuity of λ, a hypothesis of Theorem 3 → a hypothesis of the lemma; reason: Appendix A.3 proves the lemma under Theorem 3's hypotheses, and the proof uses the Lipschitz constant β (p. 37)
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 36, Appendix A.3, Lemma 5 (proof pp. 36–38, eqs. (A.4)–(A.7))

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Cutoff
import Definitions.Def_ForwardRM_Cutoffs_Supplement_ContinuousModel

namespace ForwardRM.Cutoffs.Supplement

/-- Lemma 5 (Board–Skrzypacz, p. 36). If the arrival rate is Lipschitz on `[0, T]` and
`inf_{[v̲, v̄]} m′ > 0`, there are constants `α > 0` and `h₀ > 0` such that, for every
discretization with period length `h = T/n < h₀`, every number of units `k ≥ 1` and every sale date
`t = ih ≤ T − 2h` (`1 ≤ i ≤ n − 2`), the optimal cutoff falls by at most `αh` from one period to the
next: `x^k_t − x^k_{t+h} ≤ αh`. The constants are uniform in `h`, `t` and `k`. -/
theorem cutoff_drop_le (C : ContinuousModel) (hlip : C.LipschitzRate)
    (hm : C.MarginalRevenueSlopeBounded) :
    ∃ α : ℝ, 0 < α ∧ ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ (n : ℕ) (hn : 1 ≤ n), C.step n < h₀ →
        ∀ k : ℕ, 1 ≤ k → ∀ i : ℕ, 1 ≤ i → i + 2 ≤ n →
          (C.discretize n hn).cutoff i k - (C.discretize n hn).cutoff (i + 1) k ≤ α * C.step n := by sorry

end ForwardRM.Cutoffs.Supplement
