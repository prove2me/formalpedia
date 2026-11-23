-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_dualLatticeBasis_coe
-- name    : DedekindZeta.PoissonSummation.dualLatticeBasis_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:04:14.454331+00:00
-- url     : https://prove2.me/theorems/b1646399-e0cb-4380-902a-0cf447081937
-- title:
--   Poisson Summation: dual Lattice Basis coe
-- statement:
--   The Poisson Summation construction uses the dual Lattice Basis coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L746-L748
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L746-L748

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

theorem DedekindZeta.PoissonSummation.dualLatticeBasis_coe (i : Fin d) :
    ((dualLatticeBasis L b i : dualLattice L) : V) = dualBasisR L b i := by sorry
