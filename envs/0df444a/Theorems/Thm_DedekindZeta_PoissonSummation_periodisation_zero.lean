-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_periodisation_zero
-- name    : DedekindZeta.PoissonSummation.periodisation_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:01:44.502596+00:00
-- url     : https://prove2.me/theorems/c69c8fda-0d52-4345-942c-18677f8e0c2a
-- title:
--   Poisson Summation: periodisation zero
-- statement:
--   The periodisation evaluated at `0` is the lattice sum `∑_{v∈L} f v`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L201-L202
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L201-L202

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

theorem DedekindZeta.PoissonSummation.periodisation_zero : periodisation L f 0 = ∑' v : L, (f : V → ℂ) v := by sorry
