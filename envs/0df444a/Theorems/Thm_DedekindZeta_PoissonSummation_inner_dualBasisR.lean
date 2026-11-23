-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_inner_dualBasisR
-- name    : DedekindZeta.PoissonSummation.inner_dualBasisR
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:04:03.610456+00:00
-- url     : https://prove2.me/theorems/43cb8de2-0955-4c2c-8202-cff84ddbc9d4
-- title:
--   Poisson Summation: inner dual Basis R
-- statement:
--   The defining duality: `⟪x, dualBasisR i⟫` reads off the `i`-th coordinate of
--   `x` in the primal ℝ-basis `b.ofZLatticeBasis ℝ L`, i.e. equals `Φ x i`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L714-L732
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L714-L732

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

theorem DedekindZeta.PoissonSummation.inner_dualBasisR (x : V) (i : Fin d) :
    (⟪x, dualBasisR L b i⟫ : ℝ) = latticeEquivFun L b x i := by sorry
