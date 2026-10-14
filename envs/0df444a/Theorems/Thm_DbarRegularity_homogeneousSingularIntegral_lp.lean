-- Prove2me | Theorems.Thm_DbarRegularity_homogeneousSingularIntegral_lp
-- name    : DbarRegularity.homogeneousSingularIntegral_lp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T21:54:08.693678+00:00
-- url     : https://prove2.me/theorems/05d3daf2-841b-4aa8-b8c9-d8b1d6a02f75
-- title:
--   L^p boundedness of singular integrals with homogeneous Dini-continuous kernels of mean zero
-- statement:
--   Let $\Omega:\mathbb{R}^d\to\mathbb{C}$ be homogeneous of degree $0$, i.e. $\Omega(tx)=\Omega(x)$ for $t>0$, and assume
--
--   1. $\displaystyle\int_{S^{d-1}}\Omega\,d\sigma=0$, where $\sigma$ is the surface measure on the unit sphere $S^{d-1}$ (condition (24));
--   2. the modulus $w(\delta)=\sup\{|\Omega(x)-\Omega(x')|: |x|=|x'|=1,\ |x-x'|\le\delta\}$ satisfies $\displaystyle\int_0^1\frac{w(\delta)}{\delta}\,d\delta<\infty$ (condition (25)).
--
--   $\mathbb{R}^d$ carries Lebesgue measure $m$, and $\|\cdot\|_p$ is the $L^p(\mathbb{R}^d)$ norm. Let $1<p<\infty$ and for $f\in L^p(\mathbb{R}^d)$ and $\varepsilon>0$ put
--   $$T_\varepsilon f(x)=\int_{|y|\ge\varepsilon}\frac{\Omega(y)}{|y|^d}f(x-y)\,dy .$$
--   Then
--
--   (a) there is a constant $A_p$, independent of $f$ and $\varepsilon$, such that $\|T_\varepsilon f\|_p\le A_p\|f\|_p$;
--
--   (b) for each $f\in L^p$ the limit $Tf=\lim_{\varepsilon\to0}T_\varepsilon f$ exists in the $L^p$ norm, and $\|Tf\|_p\le A_p\|f\|_p$.
--
--   **Formalization Note** The sphere measure is Mathlib's `volume.toSphere` on `sphere (0 : EuclideanSpace ℝ (Fin d)) 1`; condition (24) does not change if the measure is multiplied by a positive constant. The modulus $w(\delta)$ is the supremum `⨆ … ‖Ω x - Ω x'‖ₑ` in `ℝ≥0∞`, and condition (25) is `∫⁻ δ in Ioc 0 1, w δ / ENNReal.ofReal δ < ⊤`. $T_\varepsilon f$ is the Bochner integral `∫ y in {y | ε ≤ ‖y‖}, …`; for $f\in L^p$ it converges absolutely at every $x$. The limit $\varepsilon\to0$ is taken along `𝓝[>] 0`, and the limit operator is the function `g`. `ENNReal.ofReal p` is the exponent, so $p<\infty$. The constant `A : ℝ≥0` depends on $\Omega$ and $p$. Part (c) of Stein's theorem, an explicit formula for the Fourier transform of $Tf$ when $f\in L^2$, is not included.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), ISBN 0-691-08079-8, Chapter II, § 4.2, Theorem 3 (a), (b), p. 39 (conditions (24), (25) on the same page)

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- Stein, *Singular Integrals*, Chapter II, § 4.2, Theorem 3 (a), (b) (p. 39): let `Ω` on `ℝ^d` be
homogeneous of degree `0`, with mean zero on the unit sphere `S^{d-1}` (condition (24)) and with
modulus of continuity `w(δ) = sup {|Ω(x) - Ω(x')| : |x| = |x'| = 1, |x - x'| ≤ δ}` satisfying
`∫₀¹ w(δ) / δ dδ < ∞` (condition (25)). For `1 < p < ∞`, `f ∈ L^p` and
`T_ε f (x) = ∫_{|y| ≥ ε} Ω(y) / |y|^d · f(x - y) dy`:
(a) `‖T_ε f‖_p ≤ A_p ‖f‖_p` with `A_p` independent of `f` and `ε`;
(b) `T f = lim_{ε → 0} T_ε f` exists in `L^p` and `‖T f‖_p ≤ A_p ‖f‖_p`. -/
theorem homogeneousSingularIntegral_lp {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hmean : ∫ x : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, Ω x ∂(volume.toSphere) = 0)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0,
      (∀ ε : ℝ, 0 < ε → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y in {y | ε ≤ ‖y‖}, Ω y / ((‖y‖ ^ d : ℝ) : ℂ) * f (x - y))
            (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume) ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        ∃ g : EuclideanSpace ℝ (Fin d) → ℂ, MemLp g (ENNReal.ofReal p) volume ∧
          Tendsto (fun ε : ℝ => eLpNorm
              ((fun x => ∫ y in {y | ε ≤ ‖y‖}, Ω y / ((‖y‖ ^ d : ℝ) : ℂ) * f (x - y)) - g)
              (ENNReal.ofReal p) volume)
            (𝓝[>] 0) (𝓝 0) ∧
          eLpNorm g (ENNReal.ofReal p) volume ≤ A * eLpNorm f (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
