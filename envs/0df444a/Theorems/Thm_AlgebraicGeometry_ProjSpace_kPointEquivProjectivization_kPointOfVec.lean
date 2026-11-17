-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointEquivProjectivization_kPointOfVec
-- name    : AlgebraicGeometry.ProjSpace.kPointEquivProjectivization_kPointOfVec
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:11:44.563776+00:00
-- url     : https://prove2.me/theorems/1e859dad-13f4-44b9-a994-ede414befad4
-- title:
--   The scheme point defined by a vector corresponds to its projective class
-- statement:
--   Let $K$ be a field, let $N≥0$, and let $v∈K^{N+1}$ be nonzero. Under the canonical equivalence between $K$-points of projective $N$-space and one-dimensional projective classes, $$P(v)↦[v].$$ This connects the scheme-theoretic point construction with ordinary homogeneous coordinates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry

theorem AlgebraicGeometry.ProjSpace.kPointEquivProjectivization_kPointOfVec (K : Type) [Field K] (N : ℕ)
    (v) (hv : v ≠ 0) :
    ProjSpace.kPointEquivProjectivization K N (ProjSpace.kPointOfVec K N v hv) =
      Projectivization.mk K v hv := by sorry
