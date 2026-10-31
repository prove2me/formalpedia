-- Prove2me | Theorems.Thm_DissolveCDF_lemma_3_4
-- name    : DissolveCDF.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:36:37.850984+00:00
-- url     : https://prove2.me/theorems/76a93b89-9ca8-45cd-ba06-cb29a67a3cf0
-- title:
--   Lemma 3.4 — $\mathcal A^\infty(y)$ exists, lies in $\Omega_x\cap\mathcal M$, and $\|\mathcal A^\infty(y)-y\|\le\frac{4(M_{x,A}+1)}{\sigma_{x,c}}\|c(y)\|$
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ is the objective and $c:\mathbb R^n\to\mathbb R^p$ the constraint map of the problem (OCP) $\min_x f(x)$ s.t. $c(x)=0$, with feasible set $\mathcal M=\{x: c(x)=0\}$; $\mathcal A:\mathbb R^n\to\mathbb R^n$ is a constraint dissolving operator, and $f,c,\mathcal A$ satisfy Assumptions 1.1 and 1.2.
--
--   Assume $p\ge1$ and let $x\in\mathcal M$. For every $y\in\bar\Omega_x$:
--
--   1. the iterates $\mathcal A^k(y)$ converge as $k\to\infty$, to $\mathcal A^\infty(y)$;
--   2. $\mathcal A^\infty(y)\in\Omega_x\cap\mathcal M$;
--   3. moreover,
--
--   $$
--   \|\mathcal A^\infty(y)-y\|\ \le\ \frac{4(M_{x,A}+1)}{\sigma_{x,c}}\|c(y)\|. \tag{3.7}
--   $$
--
--   Repeatedly applying $\mathcal A$ from a point near $\mathcal M$ produces a feasible point close to it.
--
--   Differences from the source:
--   - encoding: p is the dimension of ℝᵖ (σ_min of an n×0 matrix is undefined) → hypothesis 1 ≤ p; reason: excludes only p = 0, where σ_{x,c} and the constants built on it are undefined
--   - encoding: ε_x = min{ρ_x/2, σ/(32L_{x,c}(M_{x,A}+1)), σ²/(8L_{x,b}M_{x,c})} → largest ε ∈ (0, ρ_x/2] with 32L_{x,c}(M_{x,A}+1)ε ≤ σ and 8L_{x,b}M_{x,c}ε ≤ σ²; reason: equals the printed min with σ/0 = +∞; Lean's σ/0 = 0 would collapse Ω_x to {x}
--   - encoding: ρ_x as argmax, M_{x,·} and L_{x,·} as suprema → sSup of the feasible radii and of the image / difference-quotient sets over Θ_x; reason: the sets are nonempty and bounded under Assumptions 1.1–1.2, so sSup is the true supremum and the argmax
--   - encoding: A∞(y) exists → Tendsto (fun k => A^[k] y) atTop (𝓝 (Ainf A y)), with Ainf = limUnder; reason: existence of the limit is stated as convergence of the iterates to the limUnder value
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Lemma 3.4, (3.7), p.9 (proof Appendix A.1, pp.20–21)

import Mathlib
import Definitions.Def_DissolveCDF_Assumption11
import Definitions.Def_DissolveCDF_Assumption12
import Definitions.Def_DissolveCDF_sigmaXC
import Definitions.Def_DissolveCDF_MXA
import Definitions.Def_DissolveCDF_epsX
import Definitions.Def_DissolveCDF_omegaBarRadius
import Definitions.Def_DissolveCDF_Ainf
open Filter
open Topology

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Lemma 3.4, p.9 (proof Appendix A.1, pp.20–21): for any given `x ∈ M` and any
`y ∈ Ω̄_x`, `A^∞(y)` exists and `A^∞(y) ∈ Ω_x ∩ M`; moreover
`‖A^∞(y) − y‖ ≤ 4(M_{x,A} + 1)/σ_{x,c} · ‖c(y)‖` (3.7).

Under the blanket Assumptions 1.1 and 1.2 (`h11`, `h12`); `hp : 1 ≤ p` excludes `p = 0`, where `σ_min` of an `n×0` matrix, hence `σ_{x,c}`, is undefined. **Formalization Note** "`A^∞(y)` exists" is the first conjunct: the iterates
`A^[k] y` converge, to `Ainf A y`. `Ω̄_x = Metric.closedBall x (omegaBarRadius c A x)`. -/
theorem lemma_3_4 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h11 : Assumption11 f c) (h12 : Assumption12 c A) (hp : 1 ≤ p)
    {x : EuclideanSpace ℝ (Fin n)} (hx : c x = 0)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Metric.closedBall x (omegaBarRadius c A x)) :
    Tendsto (fun k : ℕ => A^[k] y) atTop (𝓝 (Ainf A y)) ∧
      Ainf A y ∈ Metric.closedBall x (epsX c A x) ∧ c (Ainf A y) = 0 ∧
      ‖Ainf A y - y‖ ≤ 4 * (MXA c A x + 1) / sigmaXC c x * ‖c y‖ := by sorry

end DissolveCDF
