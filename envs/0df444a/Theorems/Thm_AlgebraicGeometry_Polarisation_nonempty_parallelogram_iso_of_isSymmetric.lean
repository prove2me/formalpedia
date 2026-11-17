-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_parallelogram_iso_of_isSymmetric
-- name    : AlgebraicGeometry.Polarisation.nonempty_parallelogram_iso_of_isSymmetric
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:30.526574+00:00
-- url     : https://prove2.me/theorems/2c2e5545-6469-4b81-819f-03b7df3b89dd
-- title:
--   A symmetric line bundle on an abelian scheme satisfies the parallelogram isomorphism
-- statement:
--   Let $k$ be algebraically closed, let $A/k$ be an abelian scheme with commutative group law, and let $L$ be an invertible symmetric module. Writing $m,d,p_1,p_2$ for addition, subtraction, and the two projections, there exists an isomorphism $$m^*L⊗d^*L≅p_1^*(L^{⊗2})⊗p_2^*(L^{⊗2}).$$ This is the geometric source of the parallelogram law for heights.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso_monoidalV2
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field_monoidalV2

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj
open AlgebraicGeometry
open AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_parallelogram_iso_of_isSymmetric (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hsym : Polarisation.IsSymmetric f L 𝓛) :
    Nonempty (((Scheme.Modules.pullback (Polarisation.addMor f L)).obj 𝓛 ⊗
        (Scheme.Modules.pullback (Polarisation.subMor f L)).obj 𝓛) ≅
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (𝓛.tensorPow 2) ⊗
        (Scheme.Modules.pullback (pullback.snd f f)).obj (𝓛.tensorPow 2))) := by sorry
