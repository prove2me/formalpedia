-- Prove2me | Theorems.Thm_AvramDividend_Classical_prod_ae_distinct_of_atomless_second
-- name    : AvramDividend.Classical.prod_ae_distinct_of_atomless_second
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:03:23.944383+00:00
-- url     : https://prove2.me/theorems/830c005e-70db-4c59-9a69-1c1bd94c86d6
-- title:
--   Two coordinates from a product measure cannot coincide almost surely when the second marginal is atomless
-- statement:
--   For any two Borel measures μ and ν on the real line, if ν is s-finite and assigns zero mass to every singleton, the diagonal {(x,y): x=y} has zero measure under the product μ×ν. Equivalently the two coordinates of the product measure are almost surely unequal. This is a necessary distributional ingredient for excluding simultaneous arrivals among independent diffuse-time Poisson marks in the canonical Lévy construction.
-- source:
--   Mathlib MeasureTheory.ae_prod_iff_ae_ae (Measure.Prod) and Measure.ae_ne for NullSingletonClass (Measure.Typeclasses.NullSingletonClass). Standard Poisson random measure no-common-time argument.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.IdentDistrib

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.prod_ae_distinct_of_atomless_second
    (μ ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν] :
    ∀ᵐ p ∂μ.prod ν, p.1 ≠ p.2 := by sorry
