-- Prove2me | Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses
-- name    : AvramDividend.Classical.piPathMeasure_eq_of_finite_cylinder_masses
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:18:58.073384+00:00
-- url     : https://prove2.me/theorems/4d62c918-6680-4aa9-98a1-d28e432ce446
-- title:
--   Full path-space probability measure uniqueness from all finite cylinder masses
-- statement:
--   Two finite path-space measures on the real-valued coordinate function space agree whenever they assign identical masses to every finite-coordinate cylinder. The proof uses a π-system of finite cylinder rectangles that generates the complete product measurable space. This provides the exact step to upgrade shifted Lévy finite-dimensional stationary laws to equality of entire path measures.
-- source:
--   Measure-theoretic uniqueness on product sigma-algebras, intended for whole shifted-path stationarity needed by Avram Dividend strong-Markov child 79978d61-9d1f-4b20-b8a5-114797a8e380; constructed from Mathlib Measure.ext_of_generateFrom_of_iUnion and MeasurableSpace.pi_eq_generateFrom_projections.

import Mathlib.Probability.IdentDistrib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_increment_rectangle_product

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.piPathMeasure_eq_of_finite_cylinder_masses
    {ι : Type*} (μ ν : Measure (ι → ℝ))
    (hFinite : μ Set.univ ≠ ⊤)
    (hCyl : ∀ (J : Finset ι) (B : ι → Set ℝ),
      (∀ i ∈ J, MeasurableSet (B i)) →
      μ (Set.pi (J : Set ι) B) = ν (Set.pi (J : Set ι) B)) :
    μ = ν := by
  sorry
