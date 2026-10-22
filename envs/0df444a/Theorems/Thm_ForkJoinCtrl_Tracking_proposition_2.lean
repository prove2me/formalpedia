-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_proposition_2
-- name    : ForkJoinCtrl.Tracking.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:45.329146+00:00
-- url     : https://prove2.me/theorems/8f6d8014-e1f2-4ca4-9bdb-cd5e2298e08a
-- title:
--   Proposition 2, p. 10 — under any admissible policies, (Q̂^r_k, Ŵ^r_i) converges weakly to (Q̃_k, W̃_i), an SRBM with data (ℝ^{a1}_+, Θ, Σ, R, 0)
-- statement:
--   Assume Assumptions 1–2 and that $\Sigma$ is positive definite. Let $(\pi^r)$ be an arbitrary sequence of admissible policies, i.e. a run of system $r$ for every $r$, each started empty. Let $Z$ be an SRBM with data $(\mathbb R^{a_1}_+,\Theta,\Sigma,R,0)$ and $(\tilde Q_k,\tilde W_i)$ the associated limit vector ($\tilde Q_k=0$ for light-traffic dedicated servers). Then
--
--   $$\big(\hat Q^r_k,\ k\in\mathcal K;\ \hat W^r_i,\ i\in\mathcal I\big)\Rightarrow\big(\tilde Q_k,\ k\in\mathcal K;\ \tilde W_i,\ i\in\mathcal I\big)$$
--
--   as processes in the Skorokhod space with the $J_1$ topology.
--
--   The dedicated queues and the shared workloads have the same diffusion limit under every admissible policy; only the split of each workload across buffers is controllable. The paper gives no proof ("follows from standard methodology").
--
--   **Formalization Note** Weak convergence is the published `PuhaWardFluid.Limit.ConvInDist` (coupling form with $J_1$ convergence almost surely, on paths indexed by $\mathbb R_+$, with the max-norm distance on $\mathbb R^{a_2}$). Positive definiteness of $\Sigma$ is the paper's own assertion on p. 10 and is a hypothesis here.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. 10, Proposition 2

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_SRBM
import Definitions.Def_PuhaWardFluid_Limit_Paths

open MeasureTheory Filter Topology
open scoped NNReal

namespace ForkJoinCtrl.Tracking

theorem proposition_2 {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hSigma : M.Sigma.PosDef)
    (run : ∀ r : ℕ, Run M r)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (Z : Ω' → ℝ → Fin M.a1 → ℝ)
    (hZ : IsSRBM P' M.Theta M.Sigma Z) :
    PuhaWardFluid.Limit.ConvInDist dist P (fun r ω (t : ℝ≥0) => (run r).bhat ω (t : ℝ))
      P' (fun ω' (t : ℝ≥0) => M.limitVec Z ω' (t : ℝ)) := by sorry

end ForkJoinCtrl.Tracking
