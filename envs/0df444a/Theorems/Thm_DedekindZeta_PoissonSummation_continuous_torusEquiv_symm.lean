-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_continuous_torusEquiv_symm
-- name    : DedekindZeta.PoissonSummation.continuous_torusEquiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:04:03.65951+00:00
-- url     : https://prove2.me/theorems/1042f367-9b48-4ede-8828-c69b3bc4dbd1
-- title:
--   Poisson Summation: continuous torus Equiv symm
-- statement:
--   The inverse torus isomorphism is continuous.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L683-L684
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L683-L684

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

theorem DedekindZeta.PoissonSummation.continuous_torusEquiv_symm : Continuous (torusEquiv L b).symm := by sorry
