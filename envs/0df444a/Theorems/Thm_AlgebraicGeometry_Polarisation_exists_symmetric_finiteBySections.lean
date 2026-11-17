-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_symmetric_finiteBySections
-- name    : AlgebraicGeometry.Polarisation.exists_symmetric_finiteBySections
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:14.934198+00:00
-- url     : https://prove2.me/theorems/9252db16-ca81-4836-b6a3-6f1f6dbbbd3a
-- title:
--   An invertible module finite by sections can be replaced by a symmetric one
-- statement:
--   Let $A→Spec(k)$ be a scheme with a relative group law $G$. If an invertible module $M$ on $A$ is finite by sections over the base, then there exists an invertible module $L$ that is also finite by sections and symmetric for $G$: $$L\text{ invertible},\quad L\text{ finite by sections},\quad [-1]^*L≅L.$$ This produces the symmetric projective data needed for the height argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Theorems.Thm_AlgebraicGeometry_Polarisation_isSymmetric_tensor_pullback_negMor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_pullback_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_symmetric_finiteBySections {k : Type} [Field k] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of k)) (G : RelativeGroupLaw k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfinite : M.FiniteBySections f) :
    ∃ L : A.Modules, Scheme.Modules.IsInvertible L ∧ L.FiniteBySections f ∧
      IsSymmetric f G L := by sorry
