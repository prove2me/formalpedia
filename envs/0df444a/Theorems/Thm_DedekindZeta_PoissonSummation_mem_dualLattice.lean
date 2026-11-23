-- Prove2me | Theorems.Thm_DedekindZeta_PoissonSummation_mem_dualLattice
-- name    : DedekindZeta.PoissonSummation.mem_dualLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:48:50.887039+00:00
-- url     : https://prove2.me/theorems/181f0c3f-62f2-4766-974b-13ea38c97b02
-- title:
--   Poisson Summation: mem dual Lattice
-- statement:
--   The Poisson Summation construction uses the mem dual Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L73-L75
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean#L73-L75

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem DedekindZeta.PoissonSummation.mem_dualLattice {L : Submodule ℤ V} {w : V} :
    w ∈ dualLattice L ↔ ∀ v ∈ L, (⟪w, v⟫ : ℝ) ∈ (1 : Submodule ℤ ℝ) := by sorry
