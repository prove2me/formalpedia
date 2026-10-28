-- Prove2me | Theorems.Thm_FirstPriceLearning_ContextLowerBound_eq_7
-- name    : FirstPriceLearning.ContextLowerBound.eq_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:12.194482+00:00
-- url     : https://prove2.me/theorems/d7c1a0c4-b0ef-462e-8d3d-f8b59a0c7180
-- title:
--   (7): regret is at least $\frac14$ times the expected number of wrong-block actions
-- statement:
--   Let $K=(\alpha+1)M\le T$ with $M\ge1$, let $\pi$ be any (randomized, non-anticipating) policy, and let $u\in\{0,1,\dots,\alpha\}^M$. Run $\pi$ on the hard instance with reward law $P^u$ against the block context sequence ($c_t=c_m=M+1-m$ for $t$ in the $m$-th block $\mathcal T_m$), and write $a_t=(i_t,j_t)$. Then
--   $$\mathbb E_u[R_T(\pi)]\ \ge\ \frac14\sum_{m=1}^M\sum_{t\in\mathcal T_m}\mathbb P_u(i_t\neq c_m).$$
--
--   This is the first of the two lower bounds combined in the proof of Theorem 6.
--
--   **Formalization Note.** The paper states (7) for $R_T=\max_u\mathbb E_u[R_T(\pi)]$; it is formalized for each $u$, which implies the printed form. Probabilities and expectations are over the policy's internal randomness and the iid reward vectors.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 23, eq. (7)

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction

open MeasureTheory

namespace FirstPriceLearning.ContextLowerBound

theorem eq_7 (M α T : ℕ) (hM : 0 < M) (hT : (α + 1) * M ≤ T)
    {U : Type} [MeasurableSpace U] (μU : Measure U) [IsProbabilityMeasure μU]
    (π : Policy M (Act M α) U) (u : Fin M → Fin (α + 1)) :
    (1 / 4 : ℝ) * ∑ t : Fin T,
        (interactionLaw μU (hardLaw M α T u) T
          {ω | (action (feedbackGraph M α) π (blockContext M T hM) ω.1 ω.2 t).1 ≠
              blockContext M T hM t}).toReal ≤
      expectedRegret (feedbackGraph M α) (hardLaw M α T u) μU π (blockContext M T hM) := by sorry

end FirstPriceLearning.ContextLowerBound
