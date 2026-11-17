-- Prove2me | Theorems.Thm_AlgebraicGeometry_Proj_exists_point_mem_ideal_iff_aeval
-- name    : AlgebraicGeometry.Proj.exists_point_mem_ideal_iff_aeval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:18.060439+00:00
-- url     : https://prove2.me/theorems/0b0e091b-6274-4a95-b259-dabf5ff84b90
-- title:
--   A nonzero vector over an extension field determines a projective-spectrum point by evaluation
-- statement:
--   Let $L/K$ be a field extension and let $z:S→L$ be nonzero. There exists a point $x$ of the projective spectrum over $K$ such that every homogeneous polynomial $p$ satisfies $$p∈I_x\iff p(z)=0,$$ and every homogeneous ideal $I$ satisfies $$I⊆I_x\iff p(z)=0\text{ for all }p∈I.$$ This turns extension-valued homogeneous coordinates into a projective point.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial
open AlgebraicGeometry
open AlgebraicGeometry.Proj

theorem AlgebraicGeometry.Proj.exists_point_mem_ideal_iff_aeval
    {K L S : Type} [Field K] [Field L] [Algebra K L]
    (z : S → L) (hz : z ≠ 0) :
    ∃ x : ProjectiveSpectrum (homogeneousSubmodule S K),
      (∀ (p : MvPolynomial S K) (d : ℕ), p.IsHomogeneous d →
        (p ∈ x.asHomogeneousIdeal ↔ aeval z p = 0)) ∧
      (∀ I : HomogeneousIdeal (homogeneousSubmodule S K),
        I ≤ x.asHomogeneousIdeal ↔ ∀ p ∈ I.toIdeal, aeval z p = 0) := by sorry
