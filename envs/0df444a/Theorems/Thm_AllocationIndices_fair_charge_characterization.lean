-- Prove2me | Theorems.Thm_AllocationIndices_fair_charge_characterization
-- name    : AllocationIndices.fair_charge_characterization
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:26:49.668093+00:00
-- url     : https://prove2.me/theorems/e14bb2c9-fb55-4b8a-b07b-6c0f1dc7549d
-- title:
--   Eq. (2.5): the Gittins index is the greatest prevailing charge under which continuing for one or more periods is not a loss
-- statement:
--   **Eq. (2.5).** $\nu(B, x) = \sup\big\{\lambda : \sup_{\tau > 0} \mathbb{E}\big[\sum_{t=0}^{\tau-1} a^t [r(x(t)) - \lambda] \,\big|\, x(0) = x\big] \ge 0\big\}$: the index is the greatest rent one would be willing to pay per period for ownership of the rewards arising from the bandit while it is continued for one or more periods.
--
--   Formally: for a bandit process on a countable state space with bounded reward and $a \in (0,1)$, for every state $x$,
--   $$\nu(B, x) = \sup\{\lambda \in \mathbb{R} : 0 \le \sup_{\tau > 0}(R_\tau(B, x) - \lambda W_\tau(B, x))\},$$
--   where the inner supremum is over all stopping times $\tau \ge 1$ and $\nu(B, x)$ is the index (2.6) of the Bandit Algorithms model. The set on the right is nonempty ($\lambda = -\sup|r|$ works with $\tau = 1$) and bounded above by $\sup|r|$, so the real supremum is genuine.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §2.5 p. 25, Eq. (2.5), and the fair-charge interpretation in the proof of Theorem 2.1 (p. 27)

import Definitions.Def_AllocationIndices_Index

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem fair_charge_characterization {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x : S) :
    gittinsIndex P r a x = sSup {lam : ℝ | 0 ≤ fairChargeProfit P r a x lam} := by sorry

end AllocationIndices
