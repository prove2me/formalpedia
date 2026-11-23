-- Prove2me | Theorems.Thm_DedekindZeta_Theta_integral_comp_continuousLinearEquiv
-- name    : DedekindZeta.Theta.integral_comp_continuousLinearEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:20:03.886791+00:00
-- url     : https://prove2.me/theorems/a8168c7c-db5e-47ca-bb90-c3c219b59809
-- title:
--   Theta: integral comp continuous Linear Equiv
-- statement:
--   **Linear change of variables for the additive Haar measure `volume`.**
--   For a continuous linear automorphism `A` of a finite-dimensional real inner
--   product space, integrating `g ∘ A` against `volume` scales the integral of `g`
--   by the absolute value of the inverse Jacobian determinant `|det A|⁻¹`. The
--   formula holds for *any* `g` (even non-integrable), since it is proved through
--   the pushforward of `volume` along the measurable equivalence `A`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2076-L2093
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L2076-L2093

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

theorem DedekindZeta.Theta.integral_comp_continuousLinearEquiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : V ≃L[ℝ] V) (g : V → F) :
    ∫ v, g (A v) = |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • ∫ u, g u := by sorry
