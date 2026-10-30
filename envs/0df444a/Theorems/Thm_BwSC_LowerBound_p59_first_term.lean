-- Prove2me | Theorems.Thm_BwSC_LowerBound_p59_first_term
-- name    : BwSC.LowerBound.p59_first_term
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:11.76582+00:00
-- url     : https://prove2.me/theorems/39879844-64bc-49b3-95ec-e53b9c31671a
-- title:
--   Appendix J, p. 59 (unstated step, omitted by the paper) — if q(S,K)+2 > log₂log₂(T/K) then ((K−r)^{2−1/(2−2^{−q})}/K)·T^{1/(2−2^{−q})} ≤ 9√(KT)
-- statement:
--   Let $K>1$ and $T\ge2K$, and suppose $q(S,K)+2>\log_2\log_2(T/K)$. Then the first term of Theorem 2 satisfies
--   $$\frac{(K-r(S,K))^{2-\frac1{2-2^{-q(S,K)}}}}{K}\,T^{\frac1{2-2^{-q(S,K)}}}\ \le\ 9\sqrt{KT}.$$
--
--   The paper's reduction on p. 59 bounds only the second term of the maximum in Theorem 2 by a multiple of $\sqrt{KT}$; this companion bound for the first term is needed for the same reduction and is not printed.
--
--   **Formalization Note** The constant $9$ is not from the paper; any absolute constant suffices for the reduction. $\log_2$ is `Real.logb 2`.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 59, Appendix J (unstated step completing the reduction)

import Mathlib
import Definitions.Def_BwSC_LowerBound_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound

/-- Appendix J, p. 59 (unstated step): if `q(S,K) + 2 > log₂ log₂ (T/K)`, then the first term of
Theorem 2 also satisfies
`((K - r)^{2 - 1/(2 - 2^{-q})}/K) T^{1/(2 - 2^{-q})} ≤ 9√(KT)`. -/
theorem p59_first_term {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T)
    (hcase : Real.logb 2 (Real.logb 2 ((T : ℝ) / K)) < (qIdx S K : ℝ) + 2) :
    rateA K S T ≤ 9 * Real.sqrt ((K : ℝ) * T) := by sorry

end BwSC.LowerBound
