-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_dualLatticeEquiv_symm_repr
-- name    : DedekindZeta.PoissonSummation.dualLatticeEquiv_symm_repr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:04:35.858108+00:00
-- url     : https://prove2.me/theorems/2a1ce473-3312-4900-abc1-b5d3b381de0c
-- title:
--   Poisson Summation: dual Lattice Equiv symm repr
-- statement:
--   **Defining property of `dualLatticeEquiv`.** Each `w ∈ dualLattice L` is the
--   ℤ-combination of the dual basis with coefficients `n = dualLatticeEquiv L b w`:
--   `(w : V) = ∑ i, (n i : ℝ) • dualBasisR i`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L761-L769
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L761-L769

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

theorem DedekindZeta.PoissonSummation.dualLatticeEquiv_symm_repr (w : dualLattice L) :
    (w : V) = ∑ i, ((dualLatticeEquiv L b w i : ℤ) : ℝ) • dualBasisR L b i := by sorry
