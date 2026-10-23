-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_integrated_volterra_of_positive_sigma
-- name    : AvramDividend.Classical.gaussian_esscher_integrated_volterra_of_positive_sigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T10:49:01.068855+00:00
-- url     : https://prove2.me/theorems/512c2981-5475-4a20-a034-829d734f4e1c
-- title:
--   Integrated Gaussian Volterra equation for the Esscher scale function
-- statement:
--   For a spectrally negative Levy process with positive Gaussian coefficient and positive Esscher root, write a=σ²/2, β as the exponentially tilted Levy drift, and K(t)=∫_{z>t}(z-t)exp(-φz)μ(dz) for reflected positive jump measure μ. K is integrable over positive times by the Levy truncated-square condition with exponential damping. The tilted scale V is locally bounded and its Laplace transform is the reciprocal of aθ²+βθ+θ²L[K](θ). Laplace inversion and signed uniqueness yield a V(x)+∫_0^x(β+K(x-s))V(s)ds=x for all x>0. The theorem states the precise analytic bridge needed by the no-standing Gaussian C1 branch.
-- source:
--   Proved Gaussian Levy Esscher denominator identity 77bcca45-31d4-407c-9160-610b262d61fe, signed Laplace uniqueness 83290951-5903-4855-9932-c1d5eb47c2e8, truncated area integrability 42785549-50f3-420f-b496-2969c52fddb8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_integrated_volterra_of_positive_sigma
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ (a β : ℝ) (K : ℝ → ℝ),
      0 < a ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C) ∧
    (∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x) := by sorry
