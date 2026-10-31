-- Prove2me | Theorems.Thm_DissolveCDF_lemma_3_1
-- name    : DissolveCDF.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:35:31.338241+00:00
-- url     : https://prove2.me/theorems/685f2cb8-9e58-4b27-a331-47cbf6c572a3
-- title:
--   Lemma 3.1 — error bound $\frac1{M_{x,c}}\|c(y)\|\le\operatorname{dist}(y,\mathcal M)\le\frac2{\sigma_{x,c}}\|c(y)\|$ on $\Omega_x$
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ is the objective and $c:\mathbb R^n\to\mathbb R^p$ the constraint map of the problem (OCP) $\min_x f(x)$ s.t. $c(x)=0$, with feasible set $\mathcal M=\{x: c(x)=0\}$; $\mathcal A:\mathbb R^n\to\mathbb R^n$ is a constraint dissolving operator, and $f,c,\mathcal A$ satisfy Assumptions 1.1 and 1.2.
--
--   Assume $p\ge1$ and let $x\in\mathcal M$. Then for every $y\in\Omega_x=\{y:\|y-x\|\le\varepsilon_x\}$,
--
--   $$
--   \frac{1}{M_{x,c}}\|c(y)\|\ \le\ \operatorname{dist}(y,\mathcal M)\ \le\ \frac{2}{\sigma_{x,c}}\|c(y)\|. \tag{3.1}
--   $$
--
--   Near the feasible manifold, the constraint violation and the distance to $\mathcal M$ are comparable; this error bound underlies every later estimate.
--
--   Differences from the source:
--   - encoding: p is the dimension of ℝᵖ (σ_min of an n×0 matrix is undefined) → hypothesis 1 ≤ p; reason: excludes only p = 0, where σ_{x,c} and the constants built on it are undefined
--   - encoding: ε_x = min{ρ_x/2, σ/(32L_{x,c}(M_{x,A}+1)), σ²/(8L_{x,b}M_{x,c})} → largest ε ∈ (0, ρ_x/2] with 32L_{x,c}(M_{x,A}+1)ε ≤ σ and 8L_{x,b}M_{x,c}ε ≤ σ²; reason: equals the printed min with σ/0 = +∞; Lean's σ/0 = 0 would collapse Ω_x to {x}
--   - encoding: ρ_x as argmax, M_{x,·} and L_{x,·} as suprema → sSup of the feasible radii and of the image / difference-quotient sets over Θ_x; reason: the sets are nonempty and bounded under Assumptions 1.1–1.2, so sSup is the true supremum and the argmax
--   - encoding: dist(y, M) := min over M of ‖y − z‖ → Metric.infDist y {z | c z = 0}; reason: M is closed and contains x, so in ℝⁿ the infimum is attained and equals the minimum
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Lemma 3.1, (3.1), p.8

import Mathlib
import Definitions.Def_DissolveCDF_Assumption11
import Definitions.Def_DissolveCDF_Assumption12
import Definitions.Def_DissolveCDF_sigmaXC
import Definitions.Def_DissolveCDF_MXc
import Definitions.Def_DissolveCDF_epsX

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Lemma 3.1, p.8: for any given `x ∈ M`, the inequalities
`(1/M_{x,c}) ‖c(y)‖ ≤ dist(y, M) ≤ (2/σ_{x,c}) ‖c(y)‖` (3.1) hold for any `y ∈ Ω_x`.

Under the blanket Assumptions 1.1 and 1.2 (`h11`, `h12`); `hp : 1 ≤ p` excludes `p = 0`, where `σ_min` of an `n×0` matrix, hence `σ_{x,c}`, is undefined. **Formalization Note** `Ω_x = Metric.closedBall x (epsX c A x)`;
`dist(y, M) = Metric.infDist y {z | c z = 0}`. -/
theorem lemma_3_1 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h11 : Assumption11 f c) (h12 : Assumption12 c A) (hp : 1 ≤ p)
    {x : EuclideanSpace ℝ (Fin n)} (hx : c x = 0)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Metric.closedBall x (epsX c A x)) :
    1 / MXc c x * ‖c y‖ ≤ Metric.infDist y {z | c z = 0} ∧
      Metric.infDist y {z | c z = 0} ≤ 2 / sigmaXC c x * ‖c y‖ := by sorry

end DissolveCDF
