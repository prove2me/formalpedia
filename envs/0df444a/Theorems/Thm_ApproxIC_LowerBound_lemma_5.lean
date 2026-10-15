-- Prove2me | Theorems.Thm_ApproxIC_LowerBound_lemma_5
-- name    : ApproxIC.LowerBound.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:18.655271+00:00
-- url     : https://prove2.me/theorems/9a85ca68-b567-49a7-820a-3990bb261df4
-- title:
--   Lemma 5, p. 59 — solutions of (ODE)-(DDE) are non-decreasing on [0, p⋆ + δ]
-- statement:
--   Let $\varepsilon>0$, $\mu>0$ and $0<\delta<p^\star$ with $\mu\le p^\star-\delta$, and let $w$ and $v^\star(\cdot\,|\,\mu,\delta)$ be the maps of §5.1. If $x$ solves the system
--   $$\dot x(v)=\frac{x(v)}{w(v)-v}\ (v\in[0,p^\star-\delta]),\quad x(0)=\frac{\varepsilon}{p^\star-\delta},\quad \dot x(v)=\frac{x(v)-x(v^\star(v))}{w(v)-v}\ (v\in[p^\star-\delta,p^\star+\delta]),$$
--   then $x$ is non-decreasing on $[0,p^\star+\delta]$.
--
--   Monotonicity of the allocation is what makes $v^\star$ a best reporting function (Proposition 3) and what bounds $x$ by its limit at $p^\star+\delta$.
--
--   **Formalization Note** The price $p^\star$ is a free real here; the lemma does not use its optimality. The hypothesis $\mu\le p^\star-\delta$ is a disclosed addition: the paper's definition of $w$ (p. 31) presumes it, and without it the delay term $x(v-\mu)$ would read $x$ at negative arguments, where the system says nothing. The paper's other standing assumption $p^\star+\delta+\mu<\bar v$ does not concern $x$ and is omitted.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 59, Appendix C.1, Lemma 5

import Mathlib
import Definitions.Def_ApproxIC_LowerBound_Setting
import Definitions.Def_ApproxIC_LowerBound_Delayed

namespace ApproxIC.LowerBound

/-- Lemma 5 (Appendix C.1, p. 59): a solution of (ODE)-(DDE) is non-decreasing on `[0, p⋆ + δ]`. -/
theorem lemma_5 (pstar μ δ ε : ℝ) (hε : 0 < ε) (hμ : 0 < μ) (hδ : 0 < δ) (hδp : δ < pstar)
    (hμp : μ ≤ pstar - δ) (x : ℝ → ℝ) (hx : IsPDSolution pstar μ δ ε x) :
    MonotoneOn x (Set.Icc 0 (pstar + δ)) := by sorry

end ApproxIC.LowerBound
