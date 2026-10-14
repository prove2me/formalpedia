-- Prove2me | Theorems.Thm_DbarRegularity_truncatedSingularIntegral_lp
-- name    : DbarRegularity.truncatedSingularIntegral_lp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T21:53:44.475813+00:00
-- url     : https://prove2.me/theorems/13f6bbb8-8804-4aec-89e9-3740675159b6
-- title:
--   Uniform L^p bounds and L^p convergence of truncated singular integrals
-- statement:
--   Let $K$ be a measurable function on $\mathbb{R}^d$ and $B\ge0$ such that
--   $$|K(x)|\le B|x|^{-d}\ (x\ne0),\qquad \int_{|x|\ge2|y|}|K(x-y)-K(x)|\,dx\le B\ (y\ne0),\qquad \int_{R_1<|x|<R_2}K(x)\,dx=0\ (0<R_1<R_2<\infty).$$
--   $\mathbb{R}^d$ carries Lebesgue measure $m$, and $\|\cdot\|_p$ is the $L^p(\mathbb{R}^d)$ norm. Let $1<p<\infty$ and for $f\in L^p(\mathbb{R}^d)$ and $\varepsilon>0$ put
--   $$T_\varepsilon f(x)=\int_{|y|\ge\varepsilon}f(x-y)K(y)\,dy .$$
--   Then there is a constant $A_p$, independent of $f$ and $\varepsilon$, such that $\|T_\varepsilon f\|_p\le A_p\|f\|_p$ for all $f\in L^p$ and $\varepsilon>0$. Moreover, for each $f\in L^p$ the limit $Tf=\lim_{\varepsilon\to0}T_\varepsilon f$ exists in the $L^p$ norm, and $\|Tf\|_p\le A_p\|f\|_p$.
--
--   **Formalization Note** $T_\varepsilon f$ is the Bochner integral `∫ y in {y | ε ≤ ‖y‖}, …`; for $f\in L^p$ it converges absolutely at every $x$. The limit $\varepsilon\to0$ is taken along `𝓝[>] 0`, and the limit operator is the function `g`. `ENNReal.ofReal p` is the exponent, so $p<\infty$. The second condition on $K$ is a lower Lebesgue integral `∫⁻`, so it also asserts integrability. Measurability of $K$ is assumed as `AEStronglyMeasurable K volume`. The constant `A : ℝ≥0` depends on $K$ and $p$ (Stein: independent of $f$ and $\varepsilon$).
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), ISBN 0-691-08079-8, Chapter II, § 3.2, Theorem 2, p. 35

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- Stein, *Singular Integrals*, Chapter II, § 3.2, Theorem 2 (p. 35): let `K` on `ℝ^d` satisfy
`|K(x)| ≤ B |x|^{-d}` for `x ≠ 0`, `∫_{|x| ≥ 2|y|} |K(x - y) - K(x)| dx ≤ B` for `y ≠ 0`
(conditions (18)), and `∫_{R₁ < |x| < R₂} K(x) dx = 0` for `0 < R₁ < R₂` (condition (19)). For
`1 < p < ∞` and `f ∈ L^p` let `T_ε f (x) = ∫_{|y| ≥ ε} f(x - y) K(y) dy`. Then
`‖T_ε f‖_p ≤ A_p ‖f‖_p` with `A_p` independent of `f` and `ε` (inequality (21)), and for each
`f ∈ L^p` the limit `T f = lim_{ε → 0} T_ε f` exists in `L^p` and also satisfies (21). -/
theorem truncatedSingularIntegral_lp {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ)
    (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK2 : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0,
      (∀ ε : ℝ, 0 < ε → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume) ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        ∃ g : EuclideanSpace ℝ (Fin d) → ℂ, MemLp g (ENNReal.ofReal p) volume ∧
          Tendsto (fun ε : ℝ => eLpNorm
              ((fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) - g) (ENNReal.ofReal p) volume)
            (𝓝[>] 0) (𝓝 0) ∧
          eLpNorm g (ENNReal.ofReal p) volume ≤ A * eLpNorm f (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
