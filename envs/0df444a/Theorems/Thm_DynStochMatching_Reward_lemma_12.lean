-- Prove2me | Theorems.Thm_DynStochMatching_Reward_lemma_12
-- name    : DynStochMatching.Reward.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T20:43:42.711612+00:00
-- url     : https://prove2.me/theorems/1c0635ee-992f-467e-95a4-bde0bb8e391c
-- title:
--   Lemma 12 — Virtual-chain stochastic dominance
-- statement:
--   For any QB-feasible flow and every nonnegative time, the virtual count process is below the actual right-limit population process in the source’s lower-orthant probability order. The same comparison is also asserted for the separate pure jump process defined by the printed matrix (28)–(29). These two upper processes are distinguished because the unsaturated labeling probabilities can disagree with the printed birth intensities (finding I3). Neither comparison is assumed in the process definitions.
--
--   Source statement:
--
--   For every $t\ge0$, $\tilde X_t\preceq\bar X_t$.
--
--   Differences from the source:
--   - generalization: a finite collection of arriving types → Fin n also permits the empty type graph; reason: the empty instance has zero rewards, flows and costs; restricting to nonempty graphs recovers every source instance
--   - generalization: a source-regime feasible flow satisfying the B.3 performance guarantee → any QB-feasible flow, also allowing mixed finite and immediate lifetime types; reason: these population comparisons do not need a reward guarantee; every source flow remains included
--   - generalization: one process described both as actual policy counts and by matrix (28)–(29) → both the actual execution comparison and the printed-generator comparison are asserted; reason: the two constructions disagree without saturation; the first conjunct retains the source policy claim and the second also retains the printed intensity-law claim
--   - reading: the virtual diagonal on PDF 48 is written as minus the sum over all states, including itself → the diagonal is minus the off-diagonal sum; reason: the ordinary generator and the coordinate generator on the same pages exclude the diagonal; conservativity fixes this evident index omission (I4)
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, Lemma 12, printed p. 48 / PDF p. 49

import Definitions.Def_DynStochMatching_Reward_CountChains

open MeasureTheory Filter
open scoped ENNReal Classical

namespace DynStochMatching.Reward

theorem lemma_12 {n : ℕ} (D : Instance n) (x : Flow n)
    (hfeasible : qbFeasible D x) (t : ℝ) (ht : 0 ≤ t) :
    lowerOrthantOrder (countProcess D x true t) (executionCounts D x t) ∧
    lowerOrthantOrder (countProcess D x true t) (countProcess D x false t) := by sorry

end DynStochMatching.Reward
