-- Prove2me | Theorems.Thm_DissolveCDF_proposition_3_13
-- name    : DissolveCDF.proposition_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:37:02.041046+00:00
-- url     : https://prove2.me/theorems/cfc4bfe1-e2c7-4156-9755-74520f1f0349
-- title:
--   Proposition 3.13 — $h(\mathcal A(y))-h(y)\le-\frac\beta8\|c(y)\|^2$ and $h(\mathcal A^\infty(y))-h(y)\le-\frac\beta4\|c(y)\|^2$ on $\bar\Omega_x$
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ is the objective and $c:\mathbb R^n\to\mathbb R^p$ the constraint map of the problem (OCP) $\min_x f(x)$ s.t. $c(x)=0$, with feasible set $\mathcal M=\{x: c(x)=0\}$; $\mathcal A:\mathbb R^n\to\mathbb R^n$ is a constraint dissolving operator, and $f,c,\mathcal A$ satisfy Assumptions 1.1 and 1.2.
--
--   Assume $p\ge1$, let $x\in\mathcal M$ and $\beta\ge\beta_x$. Then for every $y\in\bar\Omega_x$,
--
--   $$
--   h(\mathcal A(y))-h(y)\ \le\ -\frac\beta8\|c(y)\|^2, \tag{3.12}
--   $$
--
--   $$
--   h(\mathcal A^\infty(y))-h(y)\ \le\ -\frac\beta4\|c(y)\|^2. \tag{3.13}
--   $$
--
--   Applying $\mathcal A$, once or until convergence, decreases the constraint dissolving function by a multiple of the squared infeasibility.
--
--   **Formalization Note** $\mathcal A^\infty(y)$ is the `limUnder` of the iterates; that they converge on $\bar\Omega_x$ is Lemma 3.4.
--
--   Differences from the source:
--   - encoding: p is the dimension of ℝᵖ (σ_min of an n×0 matrix is undefined) → hypothesis 1 ≤ p; reason: excludes only p = 0, where σ_{x,c} and the constants built on it are undefined
--   - encoding: ε_x = min{ρ_x/2, σ/(32L_{x,c}(M_{x,A}+1)), σ²/(8L_{x,b}M_{x,c})} → largest ε ∈ (0, ρ_x/2] with 32L_{x,c}(M_{x,A}+1)ε ≤ σ and 8L_{x,b}M_{x,c}ε ≤ σ²; reason: equals the printed min with σ/0 = +∞; Lean's σ/0 = 0 would collapse Ω_x to {x}
--   - encoding: ρ_x as argmax, M_{x,·} and L_{x,·} as suprema → sSup of the feasible radii and of the image / difference-quotient sets over Θ_x; reason: the sets are nonempty and bounded under Assumptions 1.1–1.2, so sSup is the true supremum and the argmax
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Proposition 3.13, (3.12)–(3.13), p.11 (proof Appendix A.2.2, p.25)

import Mathlib
import Definitions.Def_DissolveCDF_Assumption11
import Definitions.Def_DissolveCDF_Assumption12
import Definitions.Def_DissolveCDF_omegaBarRadius
import Definitions.Def_DissolveCDF_betaX
import Definitions.Def_DissolveCDF_cdf
import Definitions.Def_DissolveCDF_Ainf

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Proposition 3.13, p.11 (proof Appendix A.2.2, p.25): for any given `x ∈ M` and
`β ≥ β_x`, for any `y ∈ Ω̄_x`,
`h(A(y)) − h(y) ≤ −(β/8) ‖c(y)‖²` (3.12) and `h(A^∞(y)) − h(y) ≤ −(β/4) ‖c(y)‖²` (3.13).

Under the blanket Assumptions 1.1 and 1.2 (`h11`, `h12`); `hp : 1 ≤ p` excludes `p = 0`, where `σ_min` of an `n×0` matrix, hence `σ_{x,c}`, is undefined. **Formalization Note** `A^∞(y)` is `Ainf A y`; that the iterates converge on `Ω̄_x` is
Lemma 3.4. -/
theorem proposition_3_13 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h11 : Assumption11 f c) (h12 : Assumption12 c A) (hp : 1 ≤ p)
    {x : EuclideanSpace ℝ (Fin n)} (hx : c x = 0) {β : ℝ} (hβ : betaX f c A x ≤ β)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Metric.closedBall x (omegaBarRadius c A x)) :
    cdf f c A β (A y) - cdf f c A β y ≤ -(β / 8) * ‖c y‖ ^ 2 ∧
      cdf f c A β (Ainf A y) - cdf f c A β y ≤ -(β / 4) * ‖c y‖ ^ 2 := by sorry

end DissolveCDF
