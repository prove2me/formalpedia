-- Prove2me | Theorems.Thm_FirstPriceLearning_ContextLowerBound_conclusion
-- name    : FirstPriceLearning.ContextLowerBound.conclusion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:02.722512+00:00
-- url     : https://prove2.me/theorems/3383a988-c8d7-4981-8ba9-9f9d2788a31d
-- title:
--   Proof of Theorem 6, conclusion: $R_T \ge \sqrt{KT}/(32e^3)$ on the hard instances
-- statement:
--   Let $\alpha\ge1$, $M\ge1$, $K=(\alpha+1)M$ with $K\le T^{1/3}$ (i.e. $K^3\le T$), and let $M$ divide $T$. For every (randomized, non-anticipating) policy $\pi$, its largest expected regret over the hard instances $P^u$, $u\in\{0,1,\dots,\alpha\}^M$, against the block context sequence satisfies
--   $$R_T=\max_{u}\mathbb E_u[R_T(\pi)]\ \ge\ \frac{\sqrt{KT}}{32e^3}.$$
--
--   This is the last step of the proof of Theorem 6, deduced from (8).
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 24, proof of Theorem 6 (conclusion after (8))

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction

open MeasureTheory

namespace FirstPriceLearning.ContextLowerBound

theorem conclusion (M α T : ℕ) (hα : 1 ≤ α) (hM : 0 < M) (hK : ((α + 1) * M) ^ 3 ≤ T)
    (hMT : M ∣ T) {U : Type} [MeasurableSpace U] (μU : Measure U) [IsProbabilityMeasure μU]
    (π : Policy M (Act M α) U) :
    Real.sqrt ((((α + 1) * M : ℕ) : ℝ) * T) / (32 * Real.exp 3) ≤ maxRegret M α T hM μU π := by sorry

end FirstPriceLearning.ContextLowerBound
