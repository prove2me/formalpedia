-- Prove2me | Theorems.Thm_DedekindZeta_Theta_fourier_mixedGaussian_scaling
-- name    : DedekindZeta.Theta.fourier_mixedGaussian_scaling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:21:11.807842+00:00
-- url     : https://prove2.me/theorems/273e05a9-9c10-4e52-8415-c702889db0cd
-- title:
--   Theta: fourier mixed Gaussian scaling
-- statement:
--   **Multiplicative scaling of the Minkowski Gaussian's Fourier transform.**
--   For `x ∈ K_ℝ^*` (`mixedEmbedding.norm x ≠ 0`), the multiplicative scaling
--   `v ↦ x · v` on `mixedSpace K` is `ℝ`-linear with Jacobian determinant of
--   absolute value `|N(x)| = |mixedEmbedding.norm x|`; therefore the Fourier
--   transform of `v ↦ mixedGaussian (x · v)` (read on `minkowskiSpace K` through
--   `toMinkowski`) is `|N(x)|⁻¹` times `mixedGaussian` evaluated at the inverse
--   scaling `x⁻¹ · (·)`:
--
--       𝓕 (v ↦ mixedGaussian (x · σ⁻¹ v)) w
--         = |N(x)|⁻¹ · mixedGaussian (x⁻¹ · σ⁻¹ w),
--
--   where `σ⁻¹ = (toMinkowski K).symm`. This is the `|N(x)|`-Jacobian fact the
--   kernel inversion `mixedThetaKernel_inversion` consumes;
--   it combines the change-of-variables `u = x·v` (`|det| = |N(x)|`) with the
--   self-duality `fourier_gaussV` and the conjugation-invariance of the per-place
--   absolute values (so the inverse-adjoint and `x⁻¹`-scalings agree on `gaussV`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2148-L2168
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2148-L2168

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.fourier_mixedGaussian_scaling (x : mixedEmbedding.mixedSpace K)
    (hx : mixedEmbedding.norm x ≠ 0) (w : minkowskiSpace K) :
    𝓕 (fun v : minkowskiSpace K =>
        (mixedGaussian K (x * (toMinkowski K).symm v) : ℂ)) w
      = ((|mixedEmbedding.norm x|⁻¹ : ℝ) : ℂ) *
          (mixedGaussian K (x⁻¹ * (toMinkowski K).symm w) : ℂ) := by sorry
