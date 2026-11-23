-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_integral_fundamentalDomain_periodisation
-- name    : DedekindZeta.PoissonSummation.integral_fundamentalDomain_periodisation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:03:04.311271+00:00
-- url     : https://prove2.me/theorems/68261b86-a009-4251-91a7-487e2770bfe0
-- title:
--   Poisson Summation: integral fundamental Domain periodisation
-- statement:
--   **Unfolding the Fourier coefficient integral.** For `w ∈ dualLattice L`
--   and any fundamental domain `D` of the lattice `L`, the integral of the
--   periodisation `F` against the dual character `x ↦ 𝐞(-⟪x, w⟫)` over `D` equals
--   the full Fourier transform `𝓕 f w`. (Unfold `F(x) = ∑_{v∈L} f(x+v)`; the
--   character is `L`-periodic because `⟪w, v⟫ ∈ ℤ`, so `∑_{v∈L} ∫_D = ∫_V`, the
--   full Fourier integral.) The `exp(-2πi⟪·,w⟫)` convention matches `𝓕`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L358-L426
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L358-L426

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)

theorem DedekindZeta.PoissonSummation.integral_fundamentalDomain_periodisation
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    (w : dualLattice L) :
    (∫ x in D, 𝐞 (-⟪x, (w : V)⟫) • periodisation L f x)
      = 𝓕 (f : V → ℂ) (w : V) := by sorry
