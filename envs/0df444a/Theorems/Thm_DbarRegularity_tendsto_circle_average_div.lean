-- Prove2me | Theorems.Thm_DbarRegularity_tendsto_circle_average_div
-- name    : DbarRegularity.tendsto_circle_average_div
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T20:45:56.690166+00:00
-- url     : https://prove2.me/theorems/4ef8cc95-16b7-45e8-9793-8e122cee2b4b
-- title:
--   Limit of weighted circle averages of a C^1 function on the plane
-- statement:
--   Let $f:\mathbb R^2\to\mathbb C$ be of class $C^1$ and $x\in\mathbb R^2$. Let $\sigma$ be the surface measure on the unit circle $S^1$. Then
--   $$\lim_{\varepsilon\to0^+}\frac1\varepsilon\int_{S^1}\frac{f(x-\varepsilon\omega)}{\omega_0+i\omega_1}\,d\sigma(\omega)=-\pi\Big(\frac{\partial f}{\partial x_1}(x)-i\,\frac{\partial f}{\partial x_2}(x)\Big).$$
--
--   This identifies the small-circle limit of the averages of $f$ weighted by $1/(\omega_0+i\omega_1)$ with a multiple of the complex derivative $\partial f/\partial x_1-i\,\partial f/\partial x_2$ at $x$.
--
--   **Formalization Note.** $\mathbb R^2$ is `EuclideanSpace ℝ (Fin 2)`; $\partial f/\partial x_j(x)$ is `fderiv ℝ f x (EuclideanSpace.single j 1)` with `j = 0, 1`; the circle is the subtype `sphere 0 1` with `volume.toSphere`; the limit is `Tendsto … (𝓝[>] 0)` with $1/\varepsilon$ written as the real number `ε⁻¹` coerced to `ℂ`; `ContDiff ℝ 1 f` is the hypothesis.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter III, § 1.3, Proposition 4, p. 60

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace DbarRegularity

open MeasureTheory Metric Set Filter Topology

/-- For `f ∈ C¹(ℝ²)` and `x ∈ ℝ²`, the circle averages
`ε⁻¹ ∫_{S¹} f(x - ε ω) / (ω₀ + i ω₁) dσ(ω)` converge, as `ε → 0⁺`, to
`-π (∂₁f(x) - i ∂₂f(x))`. -/
theorem tendsto_circle_average_div (f : EuclideanSpace ℝ (Fin 2) → ℂ) (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun ε : ℝ => ((ε⁻¹ : ℝ) : ℂ) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        f (x - ε • ω.1) / ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) ∂volume.toSphere)
      (𝓝[>] 0)
      (𝓝 (-(Real.pi : ℂ) * (fderiv ℝ f x (EuclideanSpace.single 0 1) -
        Complex.I * fderiv ℝ f x (EuclideanSpace.single 1 1)))) := by sorry

end DbarRegularity
