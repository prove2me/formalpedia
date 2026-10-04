-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_eq7_variance_bound
-- name    : EntropicBarrier.Universal.eq7_variance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:26:26.624158+00:00
-- url     : https://prove2.me/theorems/d1be0a34-4af2-4849-ba62-abde9ac48ed9
-- title:
--   §4, eq. (7) — $\mathrm{Var}\langle\theta/\|\theta\|,X\rangle\le\frac{n}{\|\theta\|^2}(1+\varepsilon_n)$, $X\sim p_\theta$
-- statement:
--   Let $n\ge80$, let $\mathcal K\subset\mathbb R^n$ be a convex body with canonical exponential family $p_\theta$, and let $\theta\in\mathbb R^n\setminus\{0\}$. With $Y=\langle\theta/\|\theta\|,X\rangle$, $X\sim p_\theta$,
--   $$\mathrm{Var}(Y)\le\frac{n}{\|\theta\|^2}\left(1+\varepsilon_n\right),\qquad \varepsilon_n=100\sqrt{\frac{\log n}{n}}.$$
--
--   Equivalently $\langle\Sigma(\theta)\theta,\theta\rangle\le(1+\varepsilon_n)n$, which by the reduction of (3) is the $\nu$-bound of Theorem 1.
--
--   **Formalization Note** The variance is Mathlib's `ProbabilityTheory.variance` of $x\mapsto\langle\|\theta\|^{-1}\theta,x\rangle$ under $p_\theta$, which is a probability measure (a fact, not an assumption) on which the bounded function $Y$ has finite variance. $\varepsilon_n$ is taken equal to the paper's bound $100\sqrt{\log(n)/n}$; the bound is monotone in $\varepsilon_n$, so this is the paper's claim.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 7, §4, eq. (7) (concluded p. 8)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_EntropicBarrier_Universal_ExpFamily

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem eq7_variance_bound {n : ℕ} (hn : 80 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (θ : EuclideanSpace ℝ (Fin n)) (hθ : θ ≠ 0) :
    ProbabilityTheory.variance (fun x => ⟪‖θ‖⁻¹ • θ, x⟫) (expFamily K θ) ≤
      (n : ℝ) / ‖θ‖ ^ 2 * (1 + 100 * Real.sqrt (Real.log n / n)) := by sorry

end EntropicBarrier.Universal
