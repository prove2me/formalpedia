-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_inner_dualLattice_eq_sum
-- name    : DedekindZeta.PoissonSummation.inner_dualLattice_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:05:00.752297+00:00
-- url     : https://prove2.me/theorems/cdf6273c-7454-4e4d-b8bc-bd0c73550c02
-- title:
--   Poisson Summation: inner dual Lattice eq sum
-- statement:
--   The inner product against `w ∈ dualLattice L` decomposes through `Φ`'s
--   coordinates: `⟪x, w⟫ = ∑ i, (n i) * (Φ x i)` with `n = dualLatticeEquiv L b w`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L773-L779
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L773-L779

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

theorem DedekindZeta.PoissonSummation.inner_dualLattice_eq_sum (w : dualLattice L) (x : V) :
    (⟪x, (w : V)⟫ : ℝ)
      = ∑ i, ((dualLatticeEquiv L b w i : ℤ) : ℝ) * latticeEquivFun L b x i := by sorry
