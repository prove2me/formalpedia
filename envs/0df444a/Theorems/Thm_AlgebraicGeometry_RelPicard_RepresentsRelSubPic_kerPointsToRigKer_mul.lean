-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPointsToRigKer_mul
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPointsToRigKer_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/5ce1a89d-a15e-56b0-b58b-bd022d14fbd4
-- title:
--   Multiplicativity of the dual-number kernel-point map
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme with structure morphism $c : C \to \operatorname{Spec} R$, and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c$-composite the identity. Let $D$ consist of a scheme $P$, a morphism $D.\mathrm{toBase} : P \to \operatorname{Spec} R$ and a section $D.\mathrm{zeroSection}$ of it, and let $h$ witness that $D$ represents the condition `algEquivZeroCut c ε`: $h$ provides a rigidified line bundle (the Poincaré bundle) on the base change of $C$ along $D.\mathrm{toBase}$ satisfying the fibrewise condition that for every algebraically closed field $k$ and every $k$-point of the base the restricted bundle is algebraically equivalent to zero, the universal property that every rigidified line bundle over a base $t : T \to \operatorname{Spec} R$ satisfying that fibrewise condition is the pullback of the Poincaré bundle along a unique morphism $T \to P$ over $\operatorname{Spec} R$, and a trivialisation of the pullback along the zero section. Let $A$ be a commutative $R$-algebra, and let $L$ be the relative group law on $D.\mathrm{toBase}$ obtained from $h$ and the closure of the condition under tensor products and inverses. Consider the set of morphisms $x : \operatorname{Spec} A[\varepsilon] \to P$ over $\operatorname{Spec} R$ whose restriction along `dualNumberReduction R A` (the morphism $\operatorname{Spec} A \to \operatorname{Spec} A[\varepsilon]$ induced by $A[\varepsilon] \to A$) is the unit section $L.\mathrm{one}$ at $\operatorname{Spec} A$. The assertion is: for all $x, y$ in this set, and given any proof that the product $L.\mathrm{mul}\,x\,y$ again restricts to the unit section, the class `h.kerPointsToRigKer A` of the pullback of the Poincaré bundle along $L.\mathrm{mul}\,x\,y$ equals `RigKerDualNumber.mul c ε A` — the operation induced by tensor product of rigidified line bundles — applied to the classes attached to $x$ and to $y$.
--
--   This is the statement that the map sending a point of $D$ over the dual numbers $A[\varepsilon]$, trivial modulo $\varepsilon$, to the class of the pullback of the Poincaré bundle is a homomorphism from the group law of $D$ to the tensor product on the kernel of $\operatorname{Pic}^{\mathrm{rig}}(C_{A[\varepsilon]}) \to \operatorname{Pic}^{\mathrm{rig}}(C_A)$. Together with the bijectivity of that map it identifies the tangent space of $D$ along the unit section as a group; it is cited in the naturality and additivity statement for the deformation class and in the base-change surjectivity and fibre statement for kernel points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPointsToRigKer_mul.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPointsToRigKer_mul
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (A : Type u) [CommRing A] [Algebra R A] :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h
    ∀ (x y : { x : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) D.toBase //
        dualNumberReduction R A ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1 })
      (hxy : dualNumberReduction R A ≫ (L.mul _ x.1 y.1).1 = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1),
      h.kerPointsToRigKer A ⟨L.mul _ x.1 y.1, hxy⟩ =
        RigKerDualNumber.mul c ε A (h.kerPointsToRigKer A x) (h.kerPointsToRigKer A y) := by sorry
