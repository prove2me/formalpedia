-- Prove2me | Theorems.Thm_ContinuousMultilinearMap_norm_le_of_coordinate_bound
-- name    : ContinuousMultilinearMap.norm_le_of_coordinate_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T20:08:50.539551+00:00
-- url     : https://prove2.me/theorems/24b819db-770d-42ab-8b4f-4964a5758a72
-- title:
--   Coordinate bounds control the norm of a Euclidean multilinear map
-- statement:
--   Let T be a continuous k-multilinear map from Euclidean n-space to any real normed vector space. If the norm of T evaluated on every tuple of standard basis vectors is at most M, where M is nonnegative, then its operator norm is at most n^k M. This includes k=0 and n=0, with the usual convention 0^0=1. Expand every input in the standard basis and use the coordinate bound |v_i|≤‖v‖. No differentiability assumption is needed.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, Section 1.8, printed p.10, and Theorem 1.27, printed pp.10–11, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. Supporting coordinate-calculus interface extracted from the definitions and the coordinate expansion of the Taylor differential; this is not a verbatim numbered source theorem.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
set_option autoImplicit false

theorem ContinuousMultilinearMap.norm_le_of_coordinate_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n k : ℕ}
    (T : (EuclideanSpace ℝ (Fin n)) [×k]→L[ℝ] F)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ a : Fin k → Fin n, ‖T (fun j => EuclideanSpace.single (a j) 1)‖ ≤ M) :
    ‖T‖ ≤ (n : ℝ)^k * M := by sorry
