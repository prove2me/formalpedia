-- Prove2me | Theorems.Thm_BSUMM_Rand_theorem_2_1_part_2
-- name    : BSUMM.Rand.theorem_2_1_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:16.834025+00:00
-- url     : https://prove2.me/theorems/4c4b1265-7818-4379-8eff-96421b0db0cf
-- title:
--   Theorem 2.1(2) — RBSUM-M: ‖Ex^t − q‖ → 0, ‖x^t − x^{t+1}‖ → 0, ‖x^t − x̄^t‖ → 0 and limit points are primal-dual optimal, w.p.1
-- statement:
--   Consider problem (1.1) under the standing Assumption A, approximation functions $u_k$ satisfying Assumption B, and suppose the error bound (2.4) of Lemma 2.2 holds: there is $\tau>0$ with $\operatorname{dist}(x,X(y))\le\tau\|\tilde\nabla_xL(x;y)\|$ for all $y$ and all $x\in X$. Fix a probability vector $(p_0,\dots,p_K)$ with all $p_k>0$, and run RBSUM-M (1.13): at each iteration $t\ge1$ an index $k\in\{0,\dots,K\}$ is drawn with probability $p_k$, independently of the past, from a starting point $x^1\in X$, $y^1\in\mathbb R^m$. Suppose the stepsizes $\alpha^t>0$ follow one of the rules
--
--   1. $\alpha^t=\alpha$ for all $t$, with $\alpha$ sufficiently small;
--   2. $\sum_{t=1}^\infty\alpha^t=\infty$ and $\lim_{t\to\infty}\alpha^t=0$. (2.22)
--
--   Then, with probability 1,
--
--   $$\lim_{t\to\infty}\|Ex^t-q\|=0,\qquad \lim_{t\to\infty}\|x^t-x^{t+1}\|=0,\qquad \lim_{t\to\infty}\|x^t-\bar x^t\|=0,$$
--
--   where $\bar x^t$ is the point of $X(\hat y^t)$ nearest to $x^t$ and $\hat y^t=y^{t-1}+\alpha^{t-1}(q-Ex^{t-1})$; and every limit point $(x^\infty,y^\infty)$ of $\{(x^t,y^t)\}$ is a primal and dual optimal solution: $x^\infty$ solves (1.1) and $y^\infty$ maximizes the augmented dual function $d$.
--
--   This is the main convergence result for the randomized method: it needs neither strong convexity of the objective nor a bound on the number of blocks.
--
--   **Formalization Note** "Sufficiently small" is a threshold $\bar\alpha>0$ that is chosen after the problem data, $u$, the error bound and $p$, and before the stepsizes, the probability space and the run; rule 1 is "$\alpha^t=a$ for all $t\ge1$ with $a\le\bar\alpha$". With $\alpha^t>0$, $\sum\alpha^t=\infty$ is non-summability (the term $\alpha^0$, unused by the method, does not affect it). The run is given on an arbitrary probability space $(\Omega,P)$ (`Ω : Type`) by mutually independent measurable indices $\iota_t$ with law $p$, and iterates satisfying (1.13) for every $\omega$ from the deterministic start $(x^1,y^1)$. The distance $\|x^{t+1}-\bar x^{t+1}\|$ is $\operatorname{dist}(x^{t+1},X(\hat y^{t+1}))$. "w.p.1" covers all four claims. Limit points are cluster points of the joint sequence in $\mathbb R^n\times\mathbb R^m$; no boundedness of $y^t$ is assumed or claimed.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 15, Theorem 2.1 (part 2), (2.22)

import Mathlib
import Definitions.Def_BSUMM_Rand_Setting
import Definitions.Def_BSUMM_Rand_RBSUMM

open scoped RealInnerProductSpace

open MeasureTheory Filter Topology

namespace BSUMM.Rand

/-- Theorem 2.1(2) (arXiv:1401.7079v1, p. 15): under Assumption A (standing), Assumption B and the
global error bound (2.4), for any probability vector `p > 0` there is a threshold `ᾱ > 0` such that
for every stepsize rule (i) `α^t = α ≤ ᾱ` for `t ≥ 1`, or (ii) `∑ α^t = ∞`, `α^t → 0`, and every
RBSUM-M run driven by i.i.d. indices with law `p` from `x^1 ∈ X`, `y^1`, almost surely:
`‖Ex^t - q‖ → 0`, `‖x^t - x^{t+1}‖ → 0`, `‖x^{t+1} - x̄^{t+1}‖ = dist(x^{t+1}, X(ŷ^{t+1})) → 0`, and every
limit point of `(x^t, y^t)` is a primal and dual optimal pair. -/
theorem theorem_2_1_part_2 (S : Setting) (hA : S.AssumptionA) (u : S.UFun)
    (hB : S.AssumptionB u) (hEB : ∃ τ : ℝ, 0 < τ ∧ S.ErrorBoundWith τ)
    (p : Fin (S.K + 1) → ℝ) (hp : S.IsProbVec p) :
    ∃ αbar : ℝ, 0 < αbar ∧
      ∀ α : ℕ → ℝ, (∀ t, 0 < α t) →
        ((∃ a : ℝ, a ≤ αbar ∧ ∀ t, 1 ≤ t → α t = a) ∨
          (¬ Summable α ∧ Tendsto α atTop (𝓝 0))) →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (ι : ℕ → Ω → Fin (S.K + 1)) (xs : ℕ → Ω → S.Xsp) (ys : ℕ → Ω → S.Ysp)
          (x1 : S.Xsp) (y1 : S.Ysp),
          S.IsIIDIndexProcess P p ι → x1 ∈ S.Xset →
          (∀ ω, xs 1 ω = x1 ∧ ys 1 ω = y1) →
          (∀ ω, S.IsRBSUMMPath u α (fun t => ι t ω) (fun t => xs t ω) (fun t => ys t ω)) →
          ∀ᵐ ω ∂P,
            Tendsto (fun t => ‖S.Emap (xs t ω) - S.q‖) atTop (𝓝 0) ∧
            Tendsto (fun t => ‖xs t ω - xs (t + 1) ω‖) atTop (𝓝 0) ∧
            Tendsto (fun t => Metric.infDist (xs (t + 1) ω)
              (S.Xopt (S.dualStep (xs t ω) (ys t ω) (α t)))) atTop (𝓝 0) ∧
            ∀ (xinf : S.Xsp) (yinf : S.Ysp),
              MapClusterPt (xinf, yinf) atTop (fun t => (xs t ω, ys t ω)) →
                S.IsPrimalOpt xinf ∧ S.IsDualOpt yinf := by sorry

end BSUMM.Rand
