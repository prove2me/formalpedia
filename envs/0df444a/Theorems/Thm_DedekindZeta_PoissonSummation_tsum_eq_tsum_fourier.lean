-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_tsum_eq_tsum_fourier
-- name    : DedekindZeta.PoissonSummation.tsum_eq_tsum_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:10:07.601352+00:00
-- url     : https://prove2.me/theorems/b66318ac-615e-44c8-b6f0-4b85ea123465
-- title:
--   Poisson Summation: tsum eq tsum fourier
-- statement:
--   **Lattice Poisson summation** in a finite-dimensional real inner product
--   space. For a full-rank lattice `L ⊆ V` with covolume `vol(L)`, dual lattice
--   `L* = {w | ∀ v ∈ L, ⟪w, v⟫ ∈ ℤ}`, and a Schwartz function `f : V → ℂ`,
--
--       ∑_{v ∈ L} f(v) = (1 / vol(L)) · ∑_{w ∈ L*} f̂(w),
--
--   where `f̂ = 𝓕 f` is the Fourier transform with the `exp(-2πi⟪x,ξ⟫)` convention.
--   This is the multidimensional analogue of `SchwartzMap.tsum_eq_tsum_fourier`,
--   which Mathlib only provides in one variable.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L1332-L1338
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L1332-L1338

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

theorem DedekindZeta.PoissonSummation.tsum_eq_tsum_fourier :
    ∑' v : L, (f : V → ℂ) v
      = (ZLattice.covolume L : ℂ)⁻¹ * ∑' w : dualLattice L, 𝓕 (f : V → ℂ) w := by sorry
