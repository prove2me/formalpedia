-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_dualLatticeEquiv_apply
-- name    : DedekindZeta.PoissonSummation.dualLatticeEquiv_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:04:20.410816+00:00
-- url     : https://prove2.me/theorems/b184bb19-3599-42e1-afa7-7398653f39f2
-- title:
--   Poisson Summation: dual Lattice Equiv apply
-- statement:
--   The Poisson Summation construction uses the dual Lattice Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L755-L756
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L755-L756

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

theorem DedekindZeta.PoissonSummation.dualLatticeEquiv_apply (w : dualLattice L) (i : Fin d) :
    dualLatticeEquiv L b w i = (dualLatticeBasis L b).repr w i := by sorry
