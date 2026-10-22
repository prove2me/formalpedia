-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_theorem_2
-- name    : ForkJoinCtrl.Tracking.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:11.615061+00:00
-- url     : https://prove2.me/theorems/e278a4ca-33c1-46e6-99c9-34c9239dbac9
-- title:
--   Theorem 2, p. 16 — under the LP/QP-tracking policy, lim P(Σ h_j N̂^r_j(t) > ε) = P(z(Q̃(t), W̃(t)) > ε)
-- statement:
--   Assume Assumptions 1–2 and that $\Sigma$ is positive definite. For every $r$, consider a run of system $r$ under the proposed policy (Definition 2), started empty. Let $(\tilde Q_k,\tilde W_i)$ be the limit of Proposition 2: an SRBM $Z$ with data $(\mathbb R^{a_1}_+,\Theta,\Sigma,R,0)$ in the heavy-traffic coordinates, with $\tilde Q_k=0$ for light-traffic dedicated servers. Then for all $\epsilon>0$ and $t\ge0$
--
--   $$\lim_{r\to\infty}\mathbf P\Big(\sum_{j\in\mathcal J}h_j\hat N^r_j(t)>\epsilon\Big)=\mathbf P\Big(z\big(\tilde Q_k(t),k\in\mathcal K;\ \tilde W_i(t),i\in\mathcal I\big)>\epsilon\Big).$$
--
--   By Theorem 1 of the paper the right-hand side is a lower bound for every sequence of admissible policies, so the proposed policy is asymptotically optimal for the objective (9).
--
--   **Formalization Note** The statement is for every run of the policy and every realization of the SRBM with the given data. Positive definiteness of $\Sigma$ is the paper's own assertion on p. 10 and is a hypothesis here; no continuity-point hypothesis $\mathbf P(z(\cdot)=\epsilon)=0$ is added. Probabilities are measures in $[0,\infty]$.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. 16, Theorem 2

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Policy
import Definitions.Def_ForkJoinCtrl_Tracking_SRBM

open MeasureTheory Filter Topology

namespace ForkJoinCtrl.Tracking

theorem theorem_2 {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hSigma : M.Sigma.PosDef)
    (run : ∀ r : ℕ, PolicyRun M r)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (Z : Ω' → ℝ → Fin M.a1 → ℝ)
    (hZ : IsSRBM P' M.Theta M.Sigma Z) (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun r : ℕ => P {ω | ε < ∑ j, N.h j * (run r).Nhat j ω t}) atTop
      (𝓝 (P' {ω' | ε < z N (M.limitVec Z ω' t)})) := by sorry

end ForkJoinCtrl.Tracking
