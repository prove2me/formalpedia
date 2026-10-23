-- Prove2me | Theorems.Thm_CoVaRMC_Batching_eq_6
-- name    : CoVaRMC.Batching.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:53.426462+00:00
-- url     : https://prove2.me/theorems/6db9d6c5-62b4-4c2b-890a-c5042b37211e
-- title:
--   Proof of Lemma 1, p. 7, Equation (6) — E[I{Ŷ ≤ y}] = E[F_{Y|X}(y | X_(⌈αm⌉))]
-- statement:
--   Let $(X_{i,j}, Y_{i,j})$ be i.i.d. with joint density $f$, let $\alpha \in (0,1)$ and $m \ge 1$. In the first batch $(X_{1,j}, Y_{1,j})_{j \le m}$, let $X_{(\lceil \alpha m\rceil)}$ be the $\lceil \alpha m\rceil$-th smallest of the $X$'s and let $\hat Y$ be the $Y$ paired with it. Then, with $F_{Y|X}$ the conditional distribution function of Equation (3), for every $y \in \mathbb R$,
--   $$\mathrm E\big[I\{\hat Y \le y\}\big] = \mathrm E\big[F_{Y|X}\big(y \mid X_{(\lceil \alpha m\rceil)}\big)\big].$$
--
--   The identity turns the bias of the batch indicator into a smooth functional of a single order statistic of $X$; it is the starting point of Lemma 1 and of the $O(m^{-1})$ bias bound of Lemma 3.
--
--   **Formalization Note.** $F_{Y|X}$ is formula (3) itself (with value $0$ where $f_X = 0$, a set the order statistic avoids almost surely), not a version. Assumption 1, which the page states for Lemma 1, is not used by this identity and is not assumed; only the standing model of §2 is.
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 7, proof of Lemma 1, Equation (6)

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching

/-- Proof of Lemma 1, p. 7, Equation (6): `E[I{Ŷ ≤ y}] = E[F_{Y|X}(y | X_(⌈αm⌉))]`, with `F_{Y|X}` given
by (3) and `X_(⌈αm⌉)` the `⌈αm⌉`-th order statistic of the first batch. -/
theorem eq_6 (D : JointDensity) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (m : ℕ) (hm : 0 < m) (y : ℝ) :
    pHat P S α m y = ∫ ω, D.condCDF y (Xorder S α m 0 ω) ∂P := by sorry

end CoVaRMC.Batching
