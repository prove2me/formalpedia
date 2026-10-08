-- Prove2me | Theorems.Thm_ConnesGreen_actual_column_energy_membership
-- name    : ConnesGreen.actual_column_energy_membership
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T03:45:19.620987+00:00
-- url     : https://prove2.me/theorems/6f92f06b-e52c-4a3e-8a20-dc15c6b3eda0
-- title:
--   Original actual-zero Dirichlet columns belong to the supported-test energy completion
-- statement:
--   For every positive support radius and every actual critical-strip zeta zero, the energy vector of its original explicit Dirichlet Green column belongs to the closure of the complex span of the original smooth compactly supported tests whose topological support is contained in the open window. This is the remaining completion-membership assertion, equivalent to original column realization after the proved weak-equation and metric reductions. It requires approximation in both the function and derivative L2 coordinates. The endpoint-zero Dirichlet column itself is not claimed to be an admissible compactly supported test.
-- source:
--   Canonical Green mission RG-2, https://prove2.me/theorems/5fd8e3b0-5dec-43b7-aff3-b29b946e0f93; native monocap-tech/weil b019d40205680f9761a4b0a80cbcad56ee1b606b DirichletResolvent.lean and DirichletEnergy.lean, with additive CanonicalGreenColumnReduction.lean. Original formalization reduction, not a quotation from an external theorem.

import Definitions.Def_ConnesGreen_canonical_model
open scoped BigOperators InnerProductSpace lp ENNReal Classical

theorem ConnesGreen.actual_column_energy_membership (t : ℝ) (ht : 0 < t) : ∀ ρ : ConnesRZFrontier.CriticalZeros, ConnesGreen.energyVector t (ConnesGreen.greenColumn t ρ) ∈ ConnesGreen.energySubspace t := by sorry
