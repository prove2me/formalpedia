-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_proposition_3
-- name    : ForkJoinCtrl.Tracking.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:53.761618+00:00
-- url     : https://prove2.me/theorems/94279ab7-c8fe-43e5-9f92-6477ebc3cf6f
-- title:
--   Proposition 3, p. 19 — under the proposed policy the diffusion-scaled cost stays uniformly close to z of the diffusion-scaled state on [0, T]
-- statement:
--   Assume Assumptions 1–2 and consider, for every $r$, a run of system $r$ under the proposed policy (Definition 2), started empty. For all $\epsilon,T>0$,
--
--   $$\lim_{r\to\infty}\mathbf P\Big(\Big\|\sum_{j\in\mathcal J}h_j\hat N^r_j-Z\big(\hat Q^r_k,k\in\mathcal K;\ \hat W^r_i,i\in\mathcal I\big)\Big\|_T>\epsilon\Big)=0,$$
--
--   where $Z(f)(t)=z(f(t))$ and $\|x\|_T=\sup_{0\le s\le T}|x(s)|$.
--
--   This is state-space collapse for the cost: the proposed policy achieves the LP value $z$ of the current diffusion-scaled state at all times.
--
--   **Formalization Note** $\|x\|_T>\epsilon$ is written as "for some $s\in[0,T]$, $|x(s)|>\epsilon$", which is equivalent.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. 19, Proposition 3

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Policy

open MeasureTheory Filter Topology

namespace ForkJoinCtrl.Tracking

theorem proposition_3 {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hA1 : M.Assumption1) (hA2 : M.Assumption2)
    (run : ∀ r : ℕ, PolicyRun M r) (ε T : ℝ) (hε : 0 < ε) (hT : 0 < T) :
    Tendsto (fun r : ℕ => P {ω | ∃ s ∈ Set.Icc 0 T,
        ε < |∑ j, N.h j * (run r).Nhat j ω s - z N ((run r).bhat ω s)|})
      atTop (𝓝 0) := by sorry

end ForkJoinCtrl.Tracking
