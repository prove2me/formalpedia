-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_eq_35
-- name    : ForkJoinCtrl.Tracking.eq_35
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T12:34:20.250593+00:00
-- url     : https://prove2.me/theorems/986c1d27-1d1e-418a-97c9-fdacd571a939
-- title:
--   Display (35), p. 20 — $\mathbf P(\tau^r_{iM^r}\le r^2T)\to0$: at most $O(r^2)$ review periods in $[0,r^2T]$
-- statement:
--   Assume Assumptions 1-2 and run each system $r$ under the proposed policy (Definition 2), started empty. Fix $T>0$ and a shared server $i\in\mathcal I$. Let $\tau^r_{in}\in\mathbb R_+\cup\{\infty\}$ be the start of the $n$th review period of server $i$ and $M^r:=1+\lceil(1+\bar\mu)Jr^2T\rceil$. Then
--   $$\lim_{r\to\infty}\mathbf P\big(\tau^r_{iM^r}\le r^2T\big)=0 .$$
--
--   This is display (35) of the paper. Since every $\tau^r_{in}$ with $n\ge2$ is a service-completion epoch of server $i$, the event forces at least $M^r-1$ service completions in $[0,r^2T]$, which by the functional strong law of large numbers for renewal processes has vanishing probability. So with high probability there are only $O(r^2)$ review periods in $[0,r^2T]$, and the events of Lemma 4 cover the whole horizon. The paper states the claim summed over $i\in\mathcal I$; since $\mathcal I$ is finite, the per-server form is equivalent.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, Appendix C, p. 20, display (35) (with M^r := 1 + (1 + µ̄) J r² T as on p. 20).

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Bounds

open MeasureTheory Filter Topology

namespace ForkJoinCtrl.Tracking

theorem eq_35 {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hA1 : M.Assumption1) (hA2 : M.Assumption2)
    (run : ∀ r : ℕ, PolicyRun M r) (T : ℝ) (hT : 0 < T) (i : Fin N.I) :
    Tendsto (fun r : ℕ => P {ω | (run r).tau i (N.Mr T r) ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T)})
      atTop (𝓝 0) := by sorry

end ForkJoinCtrl.Tracking
