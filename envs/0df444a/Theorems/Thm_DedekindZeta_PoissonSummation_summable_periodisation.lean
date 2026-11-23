-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_summable_periodisation
-- name    : DedekindZeta.PoissonSummation.summable_periodisation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:01:10.864438+00:00
-- url     : https://prove2.me/theorems/fe67245c-8eec-4868-86ec-153eaeaaf5d4
-- title:
--   Poisson Summation: summable periodisation
-- statement:
--   For every `x`, the family `v ↦ f (x + v)` over the lattice `L` is summable:
--   this is Schwartz rapid decay against the polynomially-bounded lattice
--   (`ZLattice.summable_norm_sub_rpow` controls `∑_{v∈L} ‖v - y‖^r` for `r < -d`,
--   and `SchwartzMap.isBigO_cocompact_zpow` bounds `f`).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L149-L184
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L149-L184

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

theorem DedekindZeta.PoissonSummation.summable_periodisation (x : V) :
    Summable fun v : L => (f : V → ℂ) (x + v) := by sorry
