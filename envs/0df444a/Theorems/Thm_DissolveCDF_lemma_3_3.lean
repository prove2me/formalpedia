-- Prove2me | Theorems.Thm_DissolveCDF_lemma_3_3
-- name    : DissolveCDF.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:35:34.832111+00:00
-- url     : https://prove2.me/theorems/9c6083b0-3635-4aec-8eb1-b0f03e31ea69
-- title:
--   Lemma 3.3 — $\|c(\mathcal A(y))\|\le\frac{4L_{x,b}}{\sigma_{x,c}^2}\|c(y)\|^2$ on $\Omega_x$
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ is the objective and $c:\mathbb R^n\to\mathbb R^p$ the constraint map of the problem (OCP) $\min_x f(x)$ s.t. $c(x)=0$, with feasible set $\mathcal M=\{x: c(x)=0\}$; $\mathcal A:\mathbb R^n\to\mathbb R^n$ is a constraint dissolving operator, and $f,c,\mathcal A$ satisfy Assumptions 1.1 and 1.2.
--
--   Assume $p\ge1$ and let $x\in\mathcal M$. Then for every $y\in\Omega_x$,
--
--   $$
--   \|c(\mathcal A(y))\|\ \le\ \frac{4L_{x,b}}{\sigma_{x,c}^2}\|c(y)\|^2. \tag{3.4}
--   $$
--
--   One application of $\mathcal A$ reduces the feasibility violation quadratically near $\mathcal M$.
--
--   Differences from the source:
--   - encoding: p is the dimension of ℝᵖ (σ_min of an n×0 matrix is undefined) → hypothesis 1 ≤ p; reason: excludes only p = 0, where σ_{x,c} and the constants built on it are undefined
--   - encoding: ε_x = min{ρ_x/2, σ/(32L_{x,c}(M_{x,A}+1)), σ²/(8L_{x,b}M_{x,c})} → largest ε ∈ (0, ρ_x/2] with 32L_{x,c}(M_{x,A}+1)ε ≤ σ and 8L_{x,b}M_{x,c}ε ≤ σ²; reason: equals the printed min with σ/0 = +∞; Lean's σ/0 = 0 would collapse Ω_x to {x}
--   - encoding: ρ_x as argmax, M_{x,·} and L_{x,·} as suprema → sSup of the feasible radii and of the image / difference-quotient sets over Θ_x; reason: the sets are nonempty and bounded under Assumptions 1.1–1.2, so sSup is the true supremum and the argmax
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Lemma 3.3, (3.4), p.9

import Mathlib
import Definitions.Def_DissolveCDF_Assumption11
import Definitions.Def_DissolveCDF_Assumption12
import Definitions.Def_DissolveCDF_sigmaXC
import Definitions.Def_DissolveCDF_LXb
import Definitions.Def_DissolveCDF_epsX

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Lemma 3.3, p.9: for any given `x ∈ M`,
`‖c(A(y))‖ ≤ 4L_{x,b}/σ_{x,c}² · ‖c(y)‖²` (3.4) for any `y ∈ Ω_x`.

Under the blanket Assumptions 1.1 and 1.2 (`h11`, `h12`); `hp : 1 ≤ p` excludes `p = 0`, where `σ_min` of an `n×0` matrix, hence `σ_{x,c}`, is undefined. -/
theorem lemma_3_3 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h11 : Assumption11 f c) (h12 : Assumption12 c A) (hp : 1 ≤ p)
    {x : EuclideanSpace ℝ (Fin n)} (hx : c x = 0)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Metric.closedBall x (epsX c A x)) :
    ‖c (A y)‖ ≤ 4 * LXb c A x / sigmaXC c x ^ 2 * ‖c y‖ ^ 2 := by sorry

end DissolveCDF
