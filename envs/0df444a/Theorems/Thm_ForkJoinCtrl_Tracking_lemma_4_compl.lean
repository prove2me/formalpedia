-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_lemma_4_compl
-- name    : ForkJoinCtrl.Tracking.lemma_4_compl
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T12:34:46.139996+00:00
-- url     : https://prove2.me/theorems/d51b914f-870a-471c-a61b-764d5d43b961
-- title:
--   Lemma 4, p. 21 (complement form) — $\mathbf P\big((\bigcap_{n\le M^r}\mathcal A^r_{in}(\epsilon_2))^c\big)\to0$
-- statement:
--   Assume Assumptions 1-2 and run each system $r$ under the proposed policy (Definition 2), started empty. Fix $T>0$, constants $C_5,C_6,C_7>0$ satisfying (37),
--   $$C_5>\max\{4\bar\lambda,2\bar\mu\},\qquad \Big(3+2(J-1)\frac{\bar\mu}{\underline\mu}\Big)C_6<C_7<0.5\,\underline\lambda ,$$
--   a number $\epsilon_2>0$ and a shared server $i\in\mathcal I$. Let $\mathcal A^r_{in}(\epsilon_2)$ be the events (36a)-(36e): the $n$th review period of server $i$ in $[0,r^2T]$ is short, the queue lengths and the QP-selected LP solution move little during it, and at its end the queue lengths are close to the LP solution. Then the probability that one of the first $M^r=1+\lceil(1+\bar\mu)Jr^2T\rceil$ review periods misbehaves vanishes:
--   $$\lim_{r\to\infty}\mathbf P\Big(\Big(\bigcap_{n=1}^{M^r}\mathcal A^r_{in}(\epsilon_2)\Big)^{c}\Big)=0 .$$
--
--   This is Lemma 4 of the paper, $\mathbf P(\bigcap_{n=1}^{M^r}\mathcal A^r_{in}(\epsilon_2))\to1$, written for the complementary event. That is the form in which it enters the proof of Proposition 3, through the second sum in (39).
--
--   **Formalization Note.** The events are built from the review epochs $\tau^r_{in}$ and the QP-selected solution process $q^{*,r}$, which the formal model does not require to be measurable, so probabilities are outer measures. For outer measures, $\mathbf P(S)\to1$ does not imply $\mathbf P(S^c)\to0$, while the converse holds by subadditivity. This complement form therefore implies the milestone `ForkJoinCtrl.Tracking.lemma_4` and is the form needed downstream.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, Appendix C, p. 21, Lemma 4 with the events (36a)-(36e) and constants (37); used in complement form in (39), p. 21.

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Bounds

open MeasureTheory Filter Topology

namespace ForkJoinCtrl.Tracking

theorem lemma_4_compl {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hA1 : M.Assumption1) (hA2 : M.Assumption2)
    (run : ∀ r : ℕ, PolicyRun M r) (T : ℝ) (hT : 0 < T)
    (C5 C6 C7 : ℝ) (hC5 : 0 < C5) (hC6 : 0 < C6) (hC7 : 0 < C7)
    (h37a : max (4 * N.lamBar) (2 * N.muBar) < C5)
    (h37b : (3 + 2 * ((N.J : ℝ) - 1) * (N.muBar / N.muMin)) * C6 < C7)
    (h37c : C7 < 0.5 * N.lamMin)
    (ε₂ : ℝ) (hε₂ : 0 < ε₂) (i : Fin N.I) :
    Tendsto (fun r : ℕ => P (⋂ n ∈ Finset.Icc 1 (N.Mr T r), (run r).Aev T C5 C6 C7 ε₂ i n)ᶜ)
      atTop (𝓝 0) := by sorry

end ForkJoinCtrl.Tracking
