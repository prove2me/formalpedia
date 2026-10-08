-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_prop_D_1
-- name    : CorreaThreshold.Adaptive.prop_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:34.621434+00:00
-- url     : https://prove2.me/theorems/d4fd1ffc-c9c7-46b5-8b7f-dd06bdff7930
-- title:
--   Proposition D.1, p. 1476 — x + x(ln x − 1)/n + ln x(x(ln x − 1) − (β − 1))/(2n²) ≥ ((n − 1)/n)x^{n/(n−1)}
-- statement:
--   Let $\beta>1.25$. For $x\in(0,1]$ and $n\ge2$,
--   $$x+\frac{x(\ln x-1)}{n}+\frac{\ln x\,\big(x(\ln x-1)-(\beta-1)\big)}{2n^2}\ \ge\ \frac{n-1}{n}\,x^{n/(n-1)}.$$
--
--   It compares one step of the recursion (9) with a second-order Taylor step of (ODE), and drives the induction in Lemma 7.
--
--   **Formalization Note** The page states no condition on $\beta$; the proposition is used under §4's standing assumption $\beta>1.25$, and that standing assumption is stated (it supplies $-(\beta-1)\ln x\ge0$). $x^{n/(n-1)}$ is the real power with positive base.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1476, Appendix D, Proposition D.1

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem prop_D_1 (β : ℝ) (hβ : 5 / 4 < β) (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : x ∈ Set.Ioc 0 1) :
    ((n : ℝ) - 1) / n * x ^ ((n : ℝ) / ((n : ℝ) - 1)) ≤
      x + x * (Real.log x - 1) / n +
        Real.log x * (x * (Real.log x - 1) - (β - 1)) / (2 * (n : ℝ) ^ 2) := by sorry

end CorreaThreshold.Adaptive
