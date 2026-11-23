-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_continuous_periodisationTorus
-- name    : DedekindZeta.PoissonSummation.continuous_periodisationTorus
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:02:08.17248+00:00
-- url     : https://prove2.me/theorems/2ae5d8d6-f6bb-4ebc-bf4b-6617aff1d882
-- title:
--   Poisson Summation: continuous periodisation Torus
-- statement:
--   The descended periodisation is continuous on the torus `V ⧸ L`
--   (from continuity of `periodisation` and the quotient topology).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L325-L328
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L325-L328

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

theorem DedekindZeta.PoissonSummation.continuous_periodisationTorus : Continuous (periodisationTorus L f) := by sorry
