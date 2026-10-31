-- Prove2me | Theorems.Thm_DissolveCDF_theorem_3_10
-- name    : DissolveCDF.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:35:26.378259+00:00
-- url     : https://prove2.me/theorems/316db3a1-14c1-4724-b1cc-de67c173bc23
-- title:
--   Theorem 3.10 — $\|\nabla h(y)\|\ge\frac{\beta\sigma_{x,c}}{8(M_{x,A}+1)}\|c(y)\|$ on $\Omega_x$; CDF stationary points there are OCP stationary (corrected: $\beta>0$)
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ is the objective and $c:\mathbb R^n\to\mathbb R^p$ the constraint map of the problem (OCP) $\min_x f(x)$ s.t. $c(x)=0$, with feasible set $\mathcal M=\{x: c(x)=0\}$; $\mathcal A:\mathbb R^n\to\mathbb R^n$ is a constraint dissolving operator, and $f,c,\mathcal A$ satisfy Assumptions 1.1 and 1.2.
--
--   Assume $p\ge1$, let $x\in\mathcal M$ and $\beta\ge\beta_x$.
--
--   1. For every $y\in\Omega_x$,
--
--   $$
--   \|\nabla h(y)\|\ \ge\ \frac{\beta\,\sigma_{x,c}}{8(M_{x,A}+1)}\,\|c(y)\|. \tag{3.11}
--   $$
--
--   2. If moreover $\beta>0$, every first-order stationary point of CDF in $\Omega_x$ is a first-order stationary point of OCP.
--
--   So, near $\mathcal M$ and above the threshold, CDF has no infeasible stationary points.
--
--   Differences from the source:
--   - encoding: p is the dimension of ℝᵖ (σ_min of an n×0 matrix is undefined) → hypothesis 1 ≤ p; reason: excludes only p = 0, where σ_{x,c} and the constants built on it are undefined
--   - encoding: ε_x = min{ρ_x/2, σ/(32L_{x,c}(M_{x,A}+1)), σ²/(8L_{x,b}M_{x,c})} → largest ε ∈ (0, ρ_x/2] with 32L_{x,c}(M_{x,A}+1)ε ≤ σ and 8L_{x,b}M_{x,c}ε ≤ σ²; reason: equals the printed min with σ/0 = +∞; Lean's σ/0 = 0 would collapse Ω_x to {x}
--   - encoding: ρ_x as argmax, M_{x,·} and L_{x,·} as suprema → sSup of the feasible radii and of the image / difference-quotient sets over Θ_x; reason: the sets are nonempty and bounded under Assumptions 1.1–1.2, so sSup is the true supremum and the argmax
--   - correction: second sentence under β ≥ β_x only → second sentence under β ≥ β_x and 0 < β; reason: β_x can be 0, and then the sentence is false: n = 2, p = 1, f ≡ 0, c(x) = x₂, A(x) = (x₁, 0), x = 0 satisfy Assumptions 1.1–1.2 with β_x = 0; with β = 0, h ≡ 0 and every y ∈ Ω_x with y₂ ≠ 0 is stationary for CDF but infeasible; the proof needs β > 0 to get ‖c(y)‖ = 0 from (A.6)
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Theorem 3.10, (3.11), p.11 (proof Appendix A.2.1, p.22)

import Mathlib
import Definitions.Def_DissolveCDF_Assumption11
import Definitions.Def_DissolveCDF_Assumption12
import Definitions.Def_DissolveCDF_sigmaXC
import Definitions.Def_DissolveCDF_MXA
import Definitions.Def_DissolveCDF_epsX
import Definitions.Def_DissolveCDF_betaX
import Definitions.Def_DissolveCDF_cdf
import Definitions.Def_DissolveCDF_IsStationaryOCP
import Definitions.Def_DissolveCDF_IsStationaryCDF

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Theorem 3.10, p.11 (proof p.22), with `β > 0` added to its second sentence: for
any given `x ∈ M` and `β ≥ β_x`, `‖∇h(y)‖ ≥ βσ_{x,c}/(8(M_{x,A} + 1)) · ‖c(y)‖` (3.11) for any
`y ∈ Ω_x`. Moreover, if also `β > 0`, any first-order stationary point of CDF in `Ω_x` is a
first-order stationary point of OCP.

Under the blanket Assumptions 1.1 and 1.2 (`h11`, `h12`); `hp : 1 ≤ p` excludes `p = 0`, where `σ_min` of an `n×0` matrix, hence `σ_{x,c}`, is undefined.

**Formalization Note** The printed second sentence assumes only `β ≥ β_x`, and `β_x` can be `0`;
with `β = β_x = 0` it is false: `n = 2`, `p = 1`, `f ≡ 0`, `c(x) = x₂`, `A(x) = (x₁, 0)`,
`x = 0` give `β_x = 0`, `h ≡ 0`, and every `y ∈ Ω_x` with `y₂ ≠ 0` is stationary for CDF but
infeasible. The printed proof needs `β > 0` to conclude `‖c(x*)‖ = 0` from (A.6). -/
theorem theorem_3_10 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h11 : Assumption11 f c) (h12 : Assumption12 c A) (hp : 1 ≤ p)
    {x : EuclideanSpace ℝ (Fin n)} (hx : c x = 0) {β : ℝ} (hβ : betaX f c A x ≤ β) :
    (∀ y ∈ Metric.closedBall x (epsX c A x),
        β * sigmaXC c x / (8 * (MXA c A x + 1)) * ‖c y‖ ≤ ‖gradient (cdf f c A β) y‖) ∧
      (0 < β → ∀ y ∈ Metric.closedBall x (epsX c A x),
        IsStationaryCDF f c A β y → IsStationaryOCP f c y) := by sorry

end DissolveCDF
