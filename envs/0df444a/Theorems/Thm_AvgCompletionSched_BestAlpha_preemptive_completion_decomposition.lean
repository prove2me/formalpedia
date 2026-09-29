-- Prove2me | Theorems.Thm_AvgCompletionSched_BestAlpha_preemptive_completion_decomposition
-- name    : AvgCompletionSched.BestAlpha.preemptive_completion_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:47:52.438001+00:00
-- url     : https://prove2.me/theorems/274d8583-2758-40db-ae6e-219a8e4569b7
-- title:
--   Lemma 2.2 — $C^P_i = T_i + \sum_{0<\beta\le1}\beta S^P_i(\beta)$
-- statement:
--   Let $P$ be any preemptive one-machine schedule of an instance with processing times $p_j>0$ and release dates $r_j\ge0$. Fix a job $J_i$. Let $T_i$ be the total idle time of $P$ before $C^P_i$, and let $x_{ij}$ be the fraction of job $J_j$ processed before $C^P_i$. Then
--   $$C^P_i=T_i+\sum_{j} x_{ij}\,p_j .$$
--
--   In the paper's notation, $S^P_i(\beta)$ is the set of jobs $J_j$ with $x_{ij}=\beta$ (and also the sum of their processing times), and the identity reads $C^P_i=T_i+\sum_{0<\beta\le1}\beta S^P_i(\beta)$: the interval $[0,C^P_i)$ splits into idle time and the pieces of the jobs processed in it.
--
--   **Formalization Note** The sum over $\beta$ is reindexed as a sum over jobs; jobs with $x_{ij}=0$ contribute $0$. $T_i$ is defined as the Lebesgue measure of the idle times in $[0,C^P_i)$, not as $C^P_i$ minus the processed amount, so that the identity is not true by definition.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 151, Lemma 2.2

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

namespace AvgCompletionSched.BestAlpha
theorem preemptive_completion_decomposition {n : ℕ} {I : Instance n}
    (P : PreemptiveSchedule I) (i : Fin n) :
    P.CP i = P.idle i + ∑ j, P.frac i j * I.p j := by sorry
end AvgCompletionSched.BestAlpha
