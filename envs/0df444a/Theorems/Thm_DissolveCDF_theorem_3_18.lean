-- Prove2me | Theorems.Thm_DissolveCDF_theorem_3_18
-- name    : DissolveCDF.theorem_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:36:12.484666+00:00
-- url     : https://prove2.me/theorems/0bba5315-5f40-4389-b920-37a75beceaf6
-- title:
--   Theorem 3.18 — near $\mathcal M$, OCP and CDF have the same local minimizers (corrected: $\beta>0$ in the second sentence)
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ is the objective and $c:\mathbb R^n\to\mathbb R^p$ the constraint map of the problem (OCP) $\min_x f(x)$ s.t. $c(x)=0$, with feasible set $\mathcal M=\{x: c(x)=0\}$; $\mathcal A:\mathbb R^n\to\mathbb R^n$ is a constraint dissolving operator, and $f,c,\mathcal A$ satisfy Assumptions 1.1 and 1.2.
--
--   Assume $p\ge1$, let $x\in\mathcal M$ and $\beta\ge\beta_x$, and let $z\in\bar\Omega_x$. With $h(y)=f(\mathcal A(y))+\frac\beta2\|c(y)\|^2$:
--
--   1. if $z$ is a local minimizer of OCP, that is $z\in\mathcal M$ and $f(w)\ge f(z)$ for all $w\in\mathcal M$ near $z$, then $z$ is a local minimizer of CDF, that is $h(w)\ge h(z)$ for all $w\in\mathbb R^n$ near $z$;
--   2. if moreover $\beta>0$ and $z$ is a local minimizer of CDF, then $z$ is a local minimizer of OCP.
--
--   The penalty $h$ is exact near the feasible manifold: above the explicit threshold $\beta_x$, unconstrained local minimization of $h$ recovers exactly the local minimizers of the constrained problem in $\bar\Omega_x$.
--
--   Differences from the source:
--   - encoding: p is the dimension of ℝᵖ (σ_min of an n×0 matrix is undefined) → hypothesis 1 ≤ p; reason: excludes only p = 0, where σ_{x,c} and the constants built on it are undefined
--   - encoding: ε_x = min{ρ_x/2, σ/(32L_{x,c}(M_{x,A}+1)), σ²/(8L_{x,b}M_{x,c})} → largest ε ∈ (0, ρ_x/2] with 32L_{x,c}(M_{x,A}+1)ε ≤ σ and 8L_{x,b}M_{x,c}ε ≤ σ²; reason: equals the printed min with σ/0 = +∞; Lean's σ/0 = 0 would collapse Ω_x to {x}
--   - encoding: ρ_x as argmax, M_{x,·} and L_{x,·} as suprema → sSup of the feasible radii and of the image / difference-quotient sets over Θ_x; reason: the sets are nonempty and bounded under Assumptions 1.1–1.2, so sSup is the true supremum and the argmax
--   - reading: local minimizer of OCP / of CDF in Ω̄_x → z ∈ Ω̄_x with (c z = 0 ∧ IsLocalMinOn f M z), resp. IsLocalMin h z (full neighbourhood in ℝⁿ); reason: the point lies in Ω̄_x and minimality is local in M for OCP and in ℝⁿ for the unconstrained CDF, as in the proof on p.29
--   - correction: second sentence under β ≥ β_x only → second sentence under β ≥ β_x and 0 < β; reason: β_x can be 0, and then the sentence is false: n = 2, p = 1, f ≡ 0, c(x) = x₂, A(x) = (x₁, 0), x = 0 satisfy Assumptions 1.1–1.2 with β_x = 0; with β = 0, h ≡ 0 and every z ∈ Ω̄_x with z₂ ≠ 0 is a local minimizer of CDF but infeasible (Ω̄_x has positive radius)
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, Theorem 3.18, p.12 (proof Appendix A.2.3, p.29)

import Mathlib
import Definitions.Def_DissolveCDF_Assumption11
import Definitions.Def_DissolveCDF_Assumption12
import Definitions.Def_DissolveCDF_omegaBarRadius
import Definitions.Def_DissolveCDF_betaX
import Definitions.Def_DissolveCDF_cdf

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Theorem 3.18, p.12 (proof Appendix A.2.3, p.29), with `β > 0` added to its second
sentence: for any given `x ∈ M` and `β ≥ β_x`, any local minimizer of OCP in `Ω̄_x` is a local
minimizer of CDF. Moreover, if also `β > 0`, any local minimizer of CDF in `Ω̄_x` is a local
minimizer of OCP.

Under the blanket Assumptions 1.1 and 1.2 (`h11`, `h12`); `hp : 1 ≤ p` excludes `p = 0`, where `σ_min` of an `n×0` matrix, hence `σ_{x,c}`, is undefined.

**Formalization Note** A local minimizer of OCP is a point `z ∈ M` with `IsLocalMinOn f M z`; a
local minimizer of CDF is a point with `IsLocalMin h z` (a full neighbourhood in `ℝⁿ`).
`Ω̄_x = Metric.closedBall x (omegaBarRadius c A x)`. The printed second sentence assumes only
`β ≥ β_x`, and `β_x` can be `0`; with `β = β_x = 0` it is false: `n = 2`, `p = 1`, `f ≡ 0`,
`c(x) = x₂`, `A(x) = (x₁, 0)`, `x = 0` give `β_x = 0`, `h ≡ 0`, and every point of `Ω̄_x` with
`y₂ ≠ 0` is a local minimizer of CDF but not feasible. -/
theorem theorem_3_18 {n p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)}
    {A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h11 : Assumption11 f c) (h12 : Assumption12 c A) (hp : 1 ≤ p)
    {x : EuclideanSpace ℝ (Fin n)} (hx : c x = 0) {β : ℝ} (hβ : betaX f c A x ≤ β)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ Metric.closedBall x (omegaBarRadius c A x)) :
    ((c z = 0 ∧ IsLocalMinOn f {w | c w = 0} z) → IsLocalMin (cdf f c A β) z) ∧
      (0 < β → IsLocalMin (cdf f c A β) z → (c z = 0 ∧ IsLocalMinOn f {w | c w = 0} z)) := by sorry

end DissolveCDF
