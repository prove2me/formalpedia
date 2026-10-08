-- Prove2me | Theorems.Thm_ConnesGreen_columnRealization_iff_membership
-- name    : ConnesGreen.columnRealization_iff_membership
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T03:45:26.353782+00:00
-- url     : https://prove2.me/theorems/ac95a164-9272-46fd-b5aa-b8a177a875a1
-- title:
--   Green realization is equivalent to original column energy membership
-- statement:
--   For every positive support radius, the complete original actual-zero column realization predicate is equivalent to membership of each original Dirichlet column energy vector in the closed complex span of original supported-test energy vectors. The weak Green equation and the equality between the ambient energy norm and the original positive Dirichlet energy remove the projection and metric clauses as independent obstructions. The original actual-zero carrier and original source, column and completion definitions are preserved; this equivalence does not assert membership or RH.
-- source:
--   Canonical Green mission RG-2, https://prove2.me/theorems/5fd8e3b0-5dec-43b7-aff3-b29b946e0f93; native monocap-tech/weil b019d40205680f9761a4b0a80cbcad56ee1b606b DirichletResolvent.lean and DirichletEnergy.lean, with additive CanonicalGreenColumnReduction.lean. Original formalization reduction, not a quotation from an external theorem.

import Definitions.Def_ConnesGreen_canonical_model
open scoped BigOperators InnerProductSpace lp ENNReal Classical

theorem ConnesGreen.columnRealization_iff_membership (t : ℝ) (ht : 0 < t) : ConnesGreen.ColumnRealization t ↔ ∀ ρ : ConnesRZFrontier.CriticalZeros, ConnesGreen.energyVector t (ConnesGreen.greenColumn t ρ) ∈ ConnesGreen.energySubspace t := by sorry
