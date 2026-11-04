-- Prove2me | Theorems.Thm_AIMInventory_UnknownRho_lemma_9_corrected
-- name    : AIMInventory.UnknownRho.lemma_9_corrected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:47.992496+00:00
-- url     : https://prove2.me/theorems/7aaea642-9b9c-4428-8130-b1440aa4e9c0
-- title:
--   Lemma 9 (corrected) — E[K(θ,z)] ≤ 1 + 2z/(E[D₁]−θ) + 8π² E[(D₁−E[D₁])⁴]/(E[D₁]−θ)⁴
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. nonnegative demands with finite positive mean and finite fourth moment, $E[D_1^4]<\infty$. For real $\theta$ and $z$ let
--   $$K(\theta,z)=\min\Big\{t\ge0 : z+\sum_{s=1}^t(\theta-D_s)\le0\Big\}\in\{0,1,2,\dots\}\cup\{\infty\}$$
--   be the first time the random walk started at $z$ with increments $\theta-D_s$ enters $(-\infty,0]$. If $\theta<E[D_1]$, then for every $z>0$
--   $$E[K(\theta,z)]\le 1+\frac{2z}{E[D_1]-\theta}+\frac{8\pi^2E\big[(D_1-E[D_1])^4\big]}{(E[D_1]-\theta)^4}.$$
--
--   The paper prints this lemma without the leading $1$:
--   $$E[K(\theta,z)]\le\frac{2z}{E[D_1]-\theta}+\frac{8\pi^2E[D_1-E[D_1]]^4}{(E[D_1]-\theta)^4},$$
--   where $E[D_1-E[D_1]]^4$ denotes the fourth central moment. As printed it is false: for deterministic demand $D_s\equiv1$, $\theta=0$ and $z=1/4$ the walk is positive at time $0$ and equals $-3/4$ at time $1$, so $K(0,1/4)=1$, while the printed right side is $1/2$. The printed proof counts the integers $s\ge0$ with $s<2z/(E[D_1]-\theta)$ as at most $2z/(E[D_1]-\theta)$; the correct count is at most $2z/(E[D_1]-\theta)+1$, which gives the statement above.
--
--   The lemma makes the first term of Theorem 8 explicit: with a finite fourth moment, the expected hitting time there is finite and depends only on $b,h,\gamma$ and the moments of demand, so that term is $O(1/T)$.
--
--   **Formalization Note.** $E[K(\theta,z)]$ is a Lebesgue integral in $[0,\infty]$ and the right side is embedded with `ENNReal.ofReal`; the right side is positive under the hypotheses. The fourth central moment is a Bochner integral, which is honest because $E[D_1^4]<\infty$ is a hypothesis.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 13, Lemma 9 (proof in Appendix D, p. 20); corrected by an additive 1

import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model

open MeasureTheory
open scoped ENNReal NNReal

namespace AIMInventory.UnknownRho

/-- Lemma 9, p. 13, corrected by the `+1` needed to count the integer
times below `2z/(E[D]-θ)`. The printed bound fails for deterministic demand
and a sufficiently small positive `z`. -/
theorem lemma_9_corrected (P : DemandLaw) (θ z : ℝ)
    (hθ : θ < CappedBaseStock.mean P) (hz : 0 < z)
    (hfourth : Integrable (fun d : ℝ≥0 => (d : ℝ) ^ 4) P.law) :
    expectedK P θ z ≤ ENNReal.ofReal
      (1 + 2 * z / (CappedBaseStock.mean P - θ) +
        8 * Real.pi ^ 2 * centralFourth P /
          (CappedBaseStock.mean P - θ) ^ 4) := by sorry

end AIMInventory.UnknownRho
