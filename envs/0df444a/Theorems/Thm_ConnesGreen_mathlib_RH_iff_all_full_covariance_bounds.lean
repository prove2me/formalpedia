-- Prove2me | Theorems.Thm_ConnesGreen_mathlib_RH_iff_all_full_covariance_bounds
-- name    : ConnesGreen.mathlib_RH_iff_all_full_covariance_bounds
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T17:20:24.271894+00:00
-- url     : https://prove2.me/theorems/81609dbd-6a82-4ffa-bfc7-5685b0794522
-- title:
--   Mathlib RH is equivalent to full original Green covariance order on every window
-- statement:
--   Mathlib’s Riemann hypothesis is equivalent to N_t N_t* ≤ P_t P_t* on the original completed Dirichlet carrier for every positive support radius t, with the unchanged complete actual-zeta-zero negative synthesis and positive synthesis. Mathlib RH excludes the negative even integers and the point 1; the already certified scope bridge handles the open critical-strip indexing exactly. This equivalence connects the complete Green operator target to the global RH statement. It does not establish either RH or the operator inequalities.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/RHSpine.lean, ConnesGreen.mathlib_RH_iff_all_full_covariance_bounds at native compiling mathematical-source commit e348db588b5acb95a2bf9bf73bc9a10890c3f92e; public signatures unfold only the unchanged WeilPositive predicate. Full original Green actors, actual-zero subtype and multiplicities preserved.

import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.mathlib_RH_iff_all_full_covariance_bounds :
    RiemannHypothesis ↔ ∀ t : ℝ, ∀ ht : 0 < t,
      canonicalNegativeSynthesis t ht ∘L (canonicalNegativeSynthesis t ht).adjoint ≤
        canonicalPositiveCovariance t ht := by sorry
