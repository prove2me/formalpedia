-- Prove2me | Theorems.Thm_ConnesGreen_energyGraph_no_derivative_only
-- name    : ConnesGreen.energyGraph_no_derivative_only
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T03:02:39.212964+00:00
-- url     : https://prove2.me/theorems/a420c059-d95b-45d7-89b3-b09704a7ce5f
-- title:
--   RG-1a — no derivative-only vector in the completed admissible energy graph
-- statement:
--   For every positive radius, the prescribed physical carrier is the closure of the complex span of the energy vectors of the original smooth admissible tests supported in the window. Prove that a vector in this closure with zero function coordinate must itself be zero. Thus no nonzero derivative-only vector appears in completing the admissible energy graph. This is the precise closability obligation: the closure of the original derivative graph has no vertical part.
--
--   The carrier, its topology, its two L2 coordinates and the supported-test class are the published canonical definitions. This target does not introduce a free Hilbert space or assume an unproved density property. The independently checked equivalence in CanonicalGreenDensity.lean identifies it exactly with the original RG-1 dense-range target; it neither weakens RG-1 nor asserts that closability has been proved.
-- source:
--   monocap-tech/weil additive ConnesGreen canonical model, CanonicalGreenDensity.lean: sourceLift_inner, sourceLift_annihilator_iff, sourceLift_dense_iff_no_derivative_only. Exact RG-1 frontier of Connes–Weil Green realization proposal 0cf97563-2f9e-4f7c-a73f-4ca6d730fddd. Source specification is the canonical energy-graph definition; functional-analytic background is the closability of differentiation on smooth Dirichlet test functions.

import Definitions.Def_ConnesGreen_canonical_model

theorem ConnesGreen.energyGraph_no_derivative_only (t : ℝ) (ht : 0 < t) : ∀ h : ConnesGreen.Physical t, (h : ConnesGreen.Ambient t) 1 = 0 → h = 0 := by sorry
