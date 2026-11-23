-- Prove2me | Theorems.Thm_DedekindZeta_Theta_fourier_comp_continuousLinearEquiv
-- name    : DedekindZeta.Theta.fourier_comp_continuousLinearEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:21:12.289581+00:00
-- url     : https://prove2.me/theorems/f5c3ecd6-2eda-479b-9767-955fee57b4ad
-- title:
--   Theta: fourier comp continuous Linear Equiv
-- statement:
--   **General Fourier linear change-of-variables law.** For a continuous linear
--   automorphism `A` of a finite-dimensional real inner product space,
--
--       𝓕 (f ∘ A) w = |det A|⁻¹ • 𝓕 f ((A⁻¹)ᴴ w),
--
--   where `(A⁻¹)ᴴ = ContinuousLinearMap.adjoint (A.symm)` is the inverse-adjoint of
--   `A`. This generalises Mathlib's `fourier_comp_linearIsometry` (the case `det = 1`
--   with `(A⁻¹)ᴴ = A`) to an arbitrary automorphism: the real-linear substitution
--   `u = A v` contributes the Jacobian `|det A|⁻¹` (`integral_comp_continuousLinearEquiv`),
--   and `⟪A.symm u, w⟫ = ⟪u, (A.symm)ᴴ w⟫` (`ContinuousLinearMap.adjoint_inner_right`)
--   moves the character argument to the inverse-adjoint.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2106-L2128
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2106-L2128

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem DedekindZeta.Theta.fourier_comp_continuousLinearEquiv (A : V ≃L[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (fun v => f (A v)) w
      = ((|(LinearMap.det (A : V →ₗ[ℝ] V))|⁻¹ : ℝ) : ℂ) •
          𝓕 f (ContinuousLinearMap.adjoint (A.symm : V →L[ℝ] V) w) := by sorry
