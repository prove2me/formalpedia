-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_lemma_4
-- name    : ForkJoinCtrl.Tracking.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:46.630253+00:00
-- url     : https://prove2.me/theorems/a0654066-682d-4606-adb7-3c001227ae4a
-- title:
--   Lemma 4, p. 21 — with probability tending to one every review period in [0, r²T] is short, stable and ends near the QP-selected LP solution
-- statement:
--   Assume Assumptions 1–2 and consider runs of the proposed policy for every $r$. Fix $T>0$ and constants $C_5,C_6,C_7>0$ with (37):
--
--   $$C_5>\max\{4\bar\lambda,2\bar\mu\},\qquad \Big(3+2(J-1)\frac{\bar\mu}{\underline\mu}\Big)C_6<C_7<0.5\underline\lambda .$$
--
--   Then for all $\epsilon_2>0$ and $i\in\mathcal I$
--
--   $$\mathbf P\Big(\bigcap_{n=1}^{M^r}\mathcal A^r_{in}(\epsilon_2)\Big)\to 1\qquad(r\to\infty).$$
--
--   This is the core estimate behind Proposition 3: on this event the queues in front of server $i$ stay within $O(\epsilon_2 r)$ of the tracking target on $[0,r^2T]$.
--
--   **Formalization Note** $T$, $C_5$–$C_7$ and $M^r=1+\lceil(1+\bar\mu)Jr^2T\rceil$ are fixed in Appendix C of the paper; here they are universally quantified parameters. The events are those of the Bounds definition.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. 21, Lemma 4, (36), (37); p. 20, M^r

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Bounds

open MeasureTheory Filter Topology

namespace ForkJoinCtrl.Tracking

theorem lemma_4 {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hA1 : M.Assumption1) (hA2 : M.Assumption2)
    (run : ∀ r : ℕ, PolicyRun M r) (T : ℝ) (hT : 0 < T)
    (C5 C6 C7 : ℝ) (hC5 : 0 < C5) (hC6 : 0 < C6) (hC7 : 0 < C7)
    (h37a : max (4 * N.lamBar) (2 * N.muBar) < C5)
    (h37b : (3 + 2 * ((N.J : ℝ) - 1) * (N.muBar / N.muMin)) * C6 < C7)
    (h37c : C7 < 0.5 * N.lamMin)
    (ε₂ : ℝ) (hε₂ : 0 < ε₂) (i : Fin N.I) :
    Tendsto (fun r : ℕ => P (⋂ n ∈ Finset.Icc 1 (N.Mr T r), (run r).Aev T C5 C6 C7 ε₂ i n))
      atTop (𝓝 1) := by sorry

end ForkJoinCtrl.Tracking
