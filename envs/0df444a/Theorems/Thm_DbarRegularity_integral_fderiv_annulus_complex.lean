-- Prove2me | Theorems.Thm_DbarRegularity_integral_fderiv_annulus_complex
-- name    : DbarRegularity.integral_fderiv_annulus_complex
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T20:25:04.820986+00:00
-- url     : https://prove2.me/theorems/7ca884c8-74f1-4884-b42c-9dee14a33329
-- title:
--   Boundary integration formula on a spherical annulus for complex-valued functions
-- statement:
--   Let $n\ge1$, $x\in\mathbb R^n$ and $0<r<R$, and let $f:\mathbb R^n\to\mathbb C$ be continuously differentiable in a neighbourhood of every point of the punctured closed ball $\overline B_R(x)\setminus\{x\}$. Put $A=B_R(x)\setminus\overline B_r(x)$. For every constant vector $v\in\mathbb R^n$,
--   $$\int_A Df(y)[v]\,dy=R^{n-1}\int_{S^{n-1}}f(x+R\omega)\langle v,\omega\rangle\,d\sigma(\omega)-r^{n-1}\int_{S^{n-1}}f(x+r\omega)\langle v,\omega\rangle\,d\sigma(\omega),$$
--   where $d\sigma$ is the surface measure on the unit sphere. No assumption is made on $f$ at the centre $x$.
--
--   **Formalization Note.** Ambient space `EuclideanSpace ℝ (Fin n)`; the regularity hypothesis is `ContDiffAt ℝ 1 f y` at each `y ∈ closedBall x R` with `y ≠ x`; the derivative is `fderiv ℝ f y v`; the sphere integrals are with respect to Mathlib's `volume.toSphere`, and the real factors $R^{n-1}$, $r^{n-1}$ and $\langle v,\omega\rangle$ are coerced to `ℂ`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter III, § 1.3, Proposition 4, p. 60

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Complex.Basic

namespace DbarRegularity

open MeasureTheory Metric Set

/-- Boundary integration formula on a spherical annulus in a constant direction, for a
complex-valued function that is `C¹` on the closed ball punctured at its centre. -/
theorem integral_fderiv_annulus_complex {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} {x : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : ∀ y ∈ closedBall x R, y ≠ x → ContDiffAt ℝ 1 f y)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y in ball x R \ closedBall x r, fderiv ℝ f y v) =
      ((R ^ (n - 1) : ℝ) : ℂ) *
          (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + R • ω.1) * ((inner ℝ v ω.1 : ℝ) : ℂ) ∂volume.toSphere)
        - ((r ^ (n - 1) : ℝ) : ℂ) *
          (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + r • ω.1) * ((inner ℝ v ω.1 : ℝ) : ℂ) ∂volume.toSphere) := by sorry

end DbarRegularity
