-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_hasSum_periodisation_fourier
-- name    : DedekindZeta.PoissonSummation.hasSum_periodisation_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:08:05.849647+00:00
-- url     : https://prove2.me/theorems/575f2f0b-fad2-48cc-b67e-3e175e290298
-- title:
--   Poisson Summation: has Sum periodisation fourier
-- statement:
--   **Multidimensional torus Fourier inversion for the periodisation.** The
--   Fourier series of the periodisation `F = periodisation L f` over the torus
--   `V ⧸ L` converges and sums to `F(x)` at every point `x`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L1315-L1321
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L1315-L1321

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

theorem DedekindZeta.PoissonSummation.hasSum_periodisation_fourier (x : V) :
    HasSum (fun w : dualLattice L =>
      𝐞 (⟪x, (w : V)⟫) •
        ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V)))
      (periodisation L f x) := by sorry
