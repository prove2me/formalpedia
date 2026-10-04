-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_skorokhod_problem_1d
-- name    : BellWilliams2001.ThresholdPolicy.skorokhod_problem_1d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:57:36.231981+00:00
-- url     : https://prove2.me/theorems/d552ce88-b345-401d-b5c1-a91edffb4515
-- title:
--   Proposition B.1 — the one-dimensional Skorokhod problem
-- statement:
--   Let $x\in\mathbf D$ with $x(0)=0$. Then there is a unique pair $(w,v)\in\mathbf D^2$ such that
--
--   1. $w(t)=x(t)+v(t)\ge0$ for all $t\ge0$,
--   2. $v$ is nondecreasing and $v(0)=0$,
--   3. $\int_{[0,\infty)}1_{(0,\infty)}(w(t))\,dv(t)=0$.
--
--   This solution is $(w^*,v^*)$, where for $t\ge0$
--   $$v^*(t)=-\inf_{0\le s\le t}x(s),\qquad w^*(t)=x(t)+v^*(t).$$
--   Moreover every pair $(w,v)\in\mathbf D^2$ satisfying 1 and 2 has $v(t)\ge v^*(t)$ and $w(t)\ge w^*(t)$ for all $t\ge0$.
--
--   The reflection map is how (41) produces the reflected Brownian motion $\tilde W^*$, and the minimality (197) gives the pathwise lower bound behind the inequality in Theorem 5.3.
--
--   **Formalization Note** Condition 3 is stated through the Lebesgue–Stieltjes measure of the nondecreasing right-continuous function $v$ extended by $v(0)=0$ to negative times: the $dv$-measure of $\{t\ge0: w(t)>0\}$ vanishes. Uniqueness is equality on $[0,\infty)$.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), p. 647, Appendix B, Proposition B.1, (196)–(197)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory

namespace BellWilliams2001.ThresholdPolicy

/-- Proposition B.1 (p. 647): the one-dimensional Skorokhod problem. For a Skorokhod path `x`
with `x(0) = 0`, the pair `(w*, v*)`, `v*(t) = −inf_{0≤s≤t} x(s)`, `w* = x + v*`, is the unique
pair `(w, v)` of Skorokhod paths with (i) `w = x + v ≥ 0`, (ii) `v` nondecreasing with `v(0) = 0`,
(iii) `∫_{[0,∞)} 1_{(0,∞)}(w(t)) dv(t) = 0`; and every pair satisfying (i) and (ii) dominates
`(w*, v*)`. Condition (iii) is stated with the Lebesgue–Stieltjes measure `dv` of the
nondecreasing right-continuous function `v` extended by `v(0) = 0` to negative times: the
`dv`-measure of `{t ≥ 0 : w(t) > 0}` is zero. -/
theorem skorokhod_problem_1d (x : ℝ → ℝ) (hx : IsCadlag x) (hx0 : x 0 = 0) :
    let vstar : ℝ → ℝ := fun t => -(⨅ s : Set.Icc (0 : ℝ) t, x s)
    let wstar : ℝ → ℝ := fun t => x t + vstar t
    let Cond : (ℝ → ℝ) → (ℝ → ℝ) → Prop := fun w v =>
      IsCadlag w ∧ IsCadlag v ∧
      (∀ t : ℝ, 0 ≤ t → w t = x t + v t ∧ 0 ≤ w t) ∧
      MonotoneOn v (Set.Ici 0) ∧ v 0 = 0
    let Compl : (ℝ → ℝ) → (ℝ → ℝ) → Prop := fun w v =>
      ∃ F : StieltjesFunction ℝ, (∀ t : ℝ, F t = v (max t 0)) ∧
        F.measure {s : ℝ | 0 ≤ s ∧ 0 < w s} = 0
    (∀ w v : ℝ → ℝ, Cond w v → Compl w v → ∀ t : ℝ, 0 ≤ t → w t = wstar t ∧ v t = vstar t) ∧
    Cond wstar vstar ∧ Compl wstar vstar ∧
    (∀ w v : ℝ → ℝ, Cond w v → ∀ t : ℝ, 0 ≤ t → vstar t ≤ v t ∧ wstar t ≤ w t) := by sorry

end BellWilliams2001.ThresholdPolicy
