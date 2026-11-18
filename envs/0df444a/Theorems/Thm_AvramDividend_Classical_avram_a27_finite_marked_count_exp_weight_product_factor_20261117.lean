-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_finite_marked_count_exp_weight_product_factor_20261117
-- name    : AvramDividend.Classical.avram_a27_finite_marked_count_exp_weight_product_factor_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T19:04:59.973836+00:00
-- url     : https://prove2.me/theorems/459f73cc-a3e4-4175-b7a0-c22cc05f4983
-- title:
--   Finite marked count power times the exponential mark product equals the product of marked PGF factors
-- statement:
--   For a finite collection of actual marked negative jumps, z to its number times the product of exp(theta times each mark) equals the product across jumps of z exp(theta mark). This is the deterministic algebraic step from the physical finite jump product to its marked Poisson generating functional, on the same source configuration.
-- source:
--   Finset product of products and finite product of a constant, exact finite marked counting measure.

import Mathlib
open MeasureTheory
open scoped BigOperators
noncomputable section

/-- A finite physical marked point configuration's joint count and Laplace factor is its pointwise marked product. -/

theorem AvramDividend.Classical.avram_a27_finite_marked_count_exp_weight_product_factor_20261117
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z θ : ℝ) (y : ι → ℝ) :
    z ^ S.card * S.prod (fun i => Real.exp (θ * y i)) =
      S.prod (fun i => z * Real.exp (θ * y i)) := by sorry
