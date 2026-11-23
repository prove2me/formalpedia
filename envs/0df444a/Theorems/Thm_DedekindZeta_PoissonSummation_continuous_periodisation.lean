-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_continuous_periodisation
-- name    : DedekindZeta.PoissonSummation.continuous_periodisation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:01:40.821192+00:00
-- url     : https://prove2.me/theorems/b5530a19-e1c8-4e04-a0d4-c5a2b9dceaba
-- title:
--   Poisson Summation: continuous periodisation
-- statement:
--   The periodisation is continuous (locally uniform convergence of the Schwartz
--   lattice sum).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L206-L300
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L206-L300

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

theorem DedekindZeta.PoissonSummation.continuous_periodisation : Continuous (periodisation L f) := by sorry
