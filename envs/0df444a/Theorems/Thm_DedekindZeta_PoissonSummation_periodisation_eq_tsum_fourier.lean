-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_periodisation_eq_tsum_fourier
-- name    : DedekindZeta.PoissonSummation.periodisation_eq_tsum_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:07:18.760046+00:00
-- url     : https://prove2.me/theorems/6ed514f7-a455-4d2a-b6bc-03383025d7b2
-- title:
--   Poisson Summation: periodisation eq tsum fourier
-- statement:
--   **Torus Fourier inversion for the periodisation.** The periodisation
--   `F = periodisation L f` is reconstructed at every point `x` by the sum of its
--   Fourier series over the dual lattice, with coefficients
--   `c_w = (vol L)⁻¹ · 𝓕 f w`. This is the multidimensional torus Fourier
--   inversion theorem, **absent from Mathlib v4.30.0** (which only has the
--   `AddCircle` one-variable `hasSum_fourier_series_of_summable`). The
--   `exp(2πi⟪x,w⟫)` synthesis convention is dual to the `exp(-2πi⟪·,w⟫)` analysis
--   convention of `𝓕`/`fourierCoeff_periodisation`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L1197-L1310
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L1197-L1310

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus ComplexConjugate
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_1176
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_1182
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
set_option maxHeartbeats 1000000

theorem DedekindZeta.PoissonSummation.periodisation_eq_tsum_fourier (x : V) :
    periodisation L f x
      = ∑' w : dualLattice L,
          𝐞 (⟪x, (w : V)⟫) •
            ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V)) := by sorry
