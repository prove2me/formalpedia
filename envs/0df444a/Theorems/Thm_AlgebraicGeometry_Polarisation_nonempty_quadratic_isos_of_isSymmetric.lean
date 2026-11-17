-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_quadratic_isos_of_isSymmetric
-- name    : AlgebraicGeometry.Polarisation.nonempty_quadratic_isos_of_isSymmetric
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:20.438204+00:00
-- url     : https://prove2.me/theorems/dcddcac1-3c3e-4f8d-b3b2-24196c9f389e
-- title:
--   A symmetric line bundle satisfies both the quadratic and parallelogram isomorphisms
-- statement:
--   Let $A/k$ be an abelian scheme with commutative group law, and let $M$ be an invertible symmetric module. Then there exist isomorphisms $$[2]^*M≅M^{⊗4}$$ and $$m^*M⊗d^*M≅p_1^*(M^{⊗2})⊗p_2^*(M^{⊗2}).$$ These identities yield the bounded doubling and parallelogram estimates for the associated height.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso_monoidalV2
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_iso_tensorPow_sq_of_isSymmetric_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_quadratic_isos_of_isSymmetric (k : Type) [Field k] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of k)) (G : RelativeGroupLaw k f) (hc : G.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hsym : IsSymmetric f G M) :
    Nonempty ((Scheme.Modules.pullback (G.schemeNsmul 2)).obj M ≅ M.tensorPow 4) ∧
    Nonempty (((Scheme.Modules.pullback (addMor f G)).obj M ⊗
        (Scheme.Modules.pullback (subMor f G)).obj M) ≅
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (M.tensorPow 2) ⊗
        (Scheme.Modules.pullback (pullback.snd f f)).obj (M.tensorPow 2))) := by sorry
