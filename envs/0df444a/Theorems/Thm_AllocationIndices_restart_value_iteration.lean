-- Prove2me | Theorems.Thm_AllocationIndices_restart_value_iteration
-- name    : AllocationIndices.restart_value_iteration
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:29:56.321168+00:00
-- url     : https://prove2.me/theorems/819856ab-cd8e-4de8-9274-b626bdfd571a
-- title:
--   §2.6.4 (Katehakis–Veinott): the restart-in-state value iteration converges to μ(ξ) = max(0, ν(B, ξ)/(1 − a))
-- statement:
--   **§2.6.4.** Fix a state $\xi$ and let $\mu(x)$ be the maximal payoff obtainable from the bandit when it starts in state $x$ and may be restarted in state $\xi$ whenever and as often as one likes; then $\mu(\xi) = \nu(B, \xi)/(1 - a)$. Katehakis and Veinott (1987) compute it by value iteration: $\mu_0(\cdot) = 0$, $\mu_{k+1}(x) = \max\{\mu_k(\xi),\ r(x) + a\sum_y P(y \mid x)\mu_k(y)\}$, and $\mu_k(\xi) \to \mu(\xi)$ as $k \to \infty$.
--
--   Formally: for a bandit process on a countable state space with bounded reward, $a \in (0,1)$ and any state $\xi$, the iteration `restartIter P r a ξ` satisfies
--   $$\lim_{k \to \infty} \mu_k(\xi) = \max\Big(0,\ \frac{\nu(B, \xi)}{1 - a}\Big).$$
--
--   **Why the maximum with $0$.** Restarting is free in the iteration ($\mu_{k+1}(x) \ge \mu_k(\xi)$ with no reward and no discounting), so restarting forever is available and the restart value is never negative: for a single state with reward $r(\xi) = c < 0$ the iteration is identically $0$ while $\nu/(1-a) = c/(1-a) < 0$. The book's derivation takes the supremum over $\tau > 0$ only, which forces at least one continuation between restarts; for a nonnegative index (in particular for nonnegative rewards) the two agree and the limit is the book's $\nu(B, \xi)/(1 - a)$. Checked on random finite chains with rewards of both signs.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §2.6.4 p. 31: the restart-in-state formulation μ(ξ) = ν(B, ξ)/(1 − a) and the value iteration μ_{k+1}(x) = max{μ_k(ξ), r(x) + a Σ_y P(y|x) μ_k(y)}, μ_0 = 0, with μ_k(ξ) → μ(ξ)

import Definitions.Def_AllocationIndices_Index

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem restart_value_iteration {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ξ : S) :
    Filter.Tendsto (fun k ↦ restartIter P r a ξ k ξ) Filter.atTop
      (nhds (max 0 (gittinsIndex P r a ξ / (1 - a)))) := by sorry

end AllocationIndices
