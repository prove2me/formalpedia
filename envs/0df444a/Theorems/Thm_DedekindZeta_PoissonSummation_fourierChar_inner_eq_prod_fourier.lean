-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_fourierChar_inner_eq_prod_fourier
-- name    : DedekindZeta.PoissonSummation.fourierChar_inner_eq_prod_fourier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:05:37.129693+00:00
-- url     : https://prove2.me/theorems/c863f07c-7a05-4cbf-9702-3bc97224770e
-- title:
--   Poisson Summation: fourier Char inner eq prod fourier
-- statement:
--   **Character correspondence.** Under `torusEquiv L b`, the dual character
--   `x ↦ 𝐞(⟪x, w⟫)` (`w ∈ dualLattice L`, the `exp(2πi⟪x,w⟫)` synthesis convention
--   dual to `𝓕`) equals the product Fourier character `∏ i, fourier (n i) (θ_i)`
--   evaluated at `θ = torusEquiv L b ↑x`, where `n = dualLatticeEquiv L b w`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L785-L805
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L785-L805

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)

theorem DedekindZeta.PoissonSummation.fourierChar_inner_eq_prod_fourier (w : dualLattice L) (x : V) :
    ((𝐞 (⟪x, (w : V)⟫) : Circle) : ℂ)
      = ∏ i, fourier (dualLatticeEquiv L b w i)
          ((torusEquiv L b (x : V ⧸ L.toAddSubgroup)) i) := by sorry
