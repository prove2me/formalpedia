-- Prove2me | Theorems.Thm_AvgRewardPMD_SPMD_kl_uniform_le_log
-- name    : AvgRewardPMD.SPMD.kl_uniform_le_log
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:08.739792+00:00
-- url     : https://prove2.me/theorems/d702ff77-8136-45dc-b3cc-0328162fff13
-- title:
--   Proof of Theorem 1, p. 12 — D(π_0, π*) ≤ log|A| for the uniform initial policy π_0
-- statement:
--   Let $\pi_0(a\mid s)=1/|\mathcal A|$ be the uniform policy, $\pi^*$ any feasible policy and $\nu\in\Delta_{|\mathcal S|}$ any distribution on states. Then
--   $$D(\pi_0,\pi^*)=\mathbb E_{s\sim\nu}\big[D^{\pi^*}_{\pi_0}(s)\big]=\sum_s\nu(s)\sum_a\pi^*(a\mid s)\log\frac{\pi^*(a\mid s)}{1/|\mathcal A|}\le\log|\mathcal A|.$$
--
--   This bounds the initial distance in the telescoped Lemma 4, and with the choice of the stepsize it yields the constants of Theorem 1.
--
--   **Formalization Note** $0\log0=0$ is built into `kl`; the second argument $1/|\mathcal A|$ is positive whenever a policy exists.
--
--   Differences from the source:
--   - generalization: ν*, the stationary distribution of the optimal policy → any distribution ν on states; reason: ν* is an instance
--   - generalization: π*, an optimal policy → any feasible policy; reason: an optimal policy is an instance
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, p. 12, proof of Theorem 1, 'the upper bound D(π0, π∗) ≤ log |A|'

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting

namespace AvgRewardPMD.SPMD

open FoundationsML.ReinforcementLearning

theorem kl_uniform_le_log {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (ν : S → ℝ) (hν : ν ∈ stdSimplex ℝ S) (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) :
    stationaryKL ν (fun _ _ => 1 / (Fintype.card A : ℝ)) πstar ≤ Real.log (Fintype.card A) := by sorry

end AvgRewardPMD.SPMD
