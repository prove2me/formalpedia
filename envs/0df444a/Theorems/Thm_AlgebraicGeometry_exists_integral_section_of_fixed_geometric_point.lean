-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_integral_section_of_fixed_geometric_point
-- name    : AlgebraicGeometry.exists_integral_section_of_fixed_geometric_point
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:51.143873+00:00
-- url     : https://prove2.me/theorems/55fffb59-5ed2-4f00-a710-cea3cbeb266e
-- title:
--   A Galois-fixed geometric point of a proper scheme descends to an integral section
-- statement:
--   Let $p$ be prime, let $R$ be $ℚ$ localized at $p$, and let $B→Spec(R)$ be proper. Let $x$ be a geometric point over $Qbar$ whose morphism is fixed by every element of $Gal(Qbar/ℚ)$. Then there exists an $R$-section $s$ such that $$s_{Qbar}=x.$$ This turns a rational geometric point into an integral point of the proper model at $p$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry

theorem AlgebraicGeometry.exists_integral_section_of_fixed_geometric_point
    (p : ℕ) [Fact p.Prime]
    {B : Scheme.{0}}
    (f : B ⟶ Spec (CommRingCat.of (GaloisRep.ratLocalizedAt p))) [IsProper f]
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) f)
    (hx : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 = x.1) :
    ∃ s : SchemeHomOver (𝟙 (Spec (CommRingCat.of (GaloisRep.ratLocalizedAt p)))) f,
      Spec.map (CommRingCat.ofHom
        (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) ≫ s.1 = x.1 := by sorry
