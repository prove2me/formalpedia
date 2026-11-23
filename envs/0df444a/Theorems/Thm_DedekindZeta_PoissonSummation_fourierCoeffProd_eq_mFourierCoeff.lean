-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_fourierCoeffProd_eq_mFourierCoeff
-- name    : DedekindZeta.PoissonSummation.fourierCoeffProd_eq_mFourierCoeff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:06:43.535805+00:00
-- url     : https://prove2.me/theorems/127ab848-23b8-4004-8b65-4e9ef13fdb48
-- title:
--   Poisson Summation: fourier Coeff Prod eq m Fourier Coeff
-- statement:
--   The conjugate-character coefficient `fourierCoeffProd` agrees with Mathlib's
--   `UnitAddTorus.mFourierCoeff` (whose integrand is the single product character
--   `mFourier (-n)`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L847-L852
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L847-L852

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus ComplexConjugate
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_828
variable {d : ℕ}

theorem DedekindZeta.PoissonSummation.fourierCoeffProd_eq_mFourierCoeff (F : (Fin d → AddCircle (1 : ℝ)) → ℂ)
    (n : Fin d → ℤ) : fourierCoeffProd F n = mFourierCoeff F n := by sorry
