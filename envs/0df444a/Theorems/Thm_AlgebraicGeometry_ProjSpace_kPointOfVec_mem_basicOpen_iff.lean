-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_mem_basicOpen_iff
-- name    : AlgebraicGeometry.ProjSpace.kPointOfVec_mem_basicOpen_iff
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:24.736486+00:00
-- url     : https://prove2.me/theorems/68a9bbd3-af0f-491d-87b0-c264a3ebbeb8
-- title:
--   A projective point lies in $D_+(X_i)$ exactly when its $i$th coordinate is nonzero
-- statement:
--   Let $v∈K^{N+1}$ be nonzero and let $i∈\{0,…,N\}$. Then $$[v]∈D_+(X_i)\iff v_i≠0.$$ This identifies projective basic opens with nonvanishing coordinate conditions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry NeronModelInfra HomogeneousLocalization
open AlgebraicGeometry
open AlgebraicGeometry.ProjSpace

theorem AlgebraicGeometry.ProjSpace.kPointOfVec_mem_basicOpen_iff (K : Type) [Field K] (N : ℕ)
    (v : Fin (N + 1) → K) (hv : v ≠ 0) (i : Fin (N + 1)) :
    (kPointOfVec K N v hv).1 (IsLocalRing.closedPoint K) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
        (MvPolynomial.X i) ↔ v i ≠ 0 := by sorry
