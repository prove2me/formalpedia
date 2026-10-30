-- Prove2me | Theorems.Thm_BwSC_LowerBound_p59_second_term
-- name    : BwSC.LowerBound.p59_second_term
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:09.600154+00:00
-- url     : https://prove2.me/theorems/0a114c78-c2ff-479b-af70-91b11c18b1e8
-- title:
--   Appendix J, p. 59 (constant corrected: 2√(KT), not √(2KT)) — if q(S,K)+2 > log₂log₂(T/K) then K^{1−1/(2−2^{−q−1})}T^{1/(2−2^{−q−1})} ≤ 2√(KT)
-- statement:
--   Let $K>1$ and $T\ge2K$, and suppose $q(S,K)+2>\log_2\log_2(T/K)$. Then the second term of Theorem 2 satisfies
--   $$K^{1-\frac{1}{2-2^{-q(S,K)-1}}}\,T^{\frac{1}{2-2^{-q(S,K)-1}}}\ \le\ 2\sqrt{KT}.$$
--
--   Outside the regime $q(S,K)+2\le\log_2\log_2(T/K)$ the rate is therefore of order $\sqrt{KT}$, and Theorem 2 follows there from the classical $\Omega(\sqrt{KT})$ minimax lower bound for multi-armed bandits.
--
--   **Formalization Note** The page ends the chain with $\sqrt{KT}\,(T/K)^{\log_{T/K}2}=\sqrt{2KT}$; in fact $(T/K)^{\log_{T/K}2}=2$, and the ratio of the left side to $\sqrt{KT}$ reaches $2^{2/3}>\sqrt2$ (for instance $q=0$ and $T/K$ close to $16$). The corrected constant $2$ is stated. $\log_2$ is `Real.logb 2`.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 59, Appendix J, the reduction display

import Mathlib
import Definitions.Def_BwSC_LowerBound_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound

/-- Appendix J, p. 59 (constant corrected from `√2` to `2`): if
`q(S,K) + 2 > log₂ log₂ (T/K)`, then
`K^{1 - 1/(2 - 2^{-q-1})} T^{1/(2 - 2^{-q-1})} ≤ 2√(KT)`. -/
theorem p59_second_term {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T)
    (hcase : Real.logb 2 (Real.logb 2 ((T : ℝ) / K)) < (qIdx S K : ℝ) + 2) :
    rateB K S T ≤ 2 * Real.sqrt ((K : ℝ) * T) := by sorry

end BwSC.LowerBound
