-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_schemeHomOver_poincare_pullbackAlong_iso_ofPoint_lineBundle_tensor_ofPoint_idealModule_of_isLocalRing
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_schemeHomOver_poincare_pullbackAlong_iso_ofPoint_lineBundle_tensor_ofPoint_idealModule_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/f25f446e-476d-5052-94e4-5fce263f2ea3
-- title:
--   A classifying point for 𝒪(v₁-v₂) over a local base
-- statement:
--   Let $R$ be a commutative ring and let $c : C \to \operatorname{Spec} R$ be a morphism of schemes that is proper, smooth of relative dimension $1$, geometrically integral and separated, and let $\varepsilon$ be a section of $c$, that is a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity. Let $D$ consist of a scheme $P$ with a structure morphism $D.\mathrm{toBase} : P \to \operatorname{Spec} R$ and a zero section $\operatorname{Spec} R \to P$ over $\operatorname{Spec} R$, and let $h$ witness that $D$ represents the cut of the $\varepsilon$-rigidified relative Picard functor of $c$ given by the condition `FibrewiseAlgEquivZero`: it provides a rigidified line bundle `h.poincare` on $C \times_R P$ satisfying that condition, the universal property that for every $t : T \to \operatorname{Spec} R$ and every $\varepsilon$-rigidified line bundle $M$ on $C\times_R T$ satisfying the condition there is a unique morphism $T \to P$ over $\operatorname{Spec} R$ along which the pullback of `h.poincare` has underlying module isomorphic to that of $M$, and the normalisation that the pullback along the zero section is isomorphic to the unit. Let $A$ be a local commutative ring, $t_A : \operatorname{Spec} A \to \operatorname{Spec} R$ a morphism, and $v_1, v_2$ two morphisms $\operatorname{Spec} A \to C$ over $t_A$. Then there exists a morphism $s_0 : \operatorname{Spec} A \to P$ with $s_0$ followed by $D.\mathrm{toBase}$ equal to $t_A$, such that the module underlying the pullback of `h.poincare` along $s_0$ is isomorphic, on $C \times_R \operatorname{Spec} A$, to the tensor product of the dual of the ideal sheaf of the graph of $v_1$ with the ideal sheaf of the graph of $v_2$, i.e. to $\mathcal O(v_1) \otimes \mathcal O(-v_2)$. Only the existence of such an isomorphism is asserted, not a choice of one.
--
--   This is the existence half of the Abel–Jacobi dictionary for a smooth proper geometrically integral relative curve: over a local base every degree-zero difference of two sections is classified by a point of the scheme representing the algebraically trivial part of the rigidified relative Picard functor, locality of $A$ being what makes the line bundle rigidifiable along $\varepsilon$. It is used in the identification of points of the Jacobian of $X_1(p)$ with divisor classes $[v_1]-[v_2]$, in particular in the comparison of such classes with their Frobenius translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_schemeHomOver_poincare_pullbackAlong_iso_ofPoint_lineBundle_tensor_ofPoint_idealModule_of_isLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_schemeHomOver_poincare_pullbackAlong_iso_ofPoint_lineBundle_tensor_ofPoint_idealModule_of_isLocalRing
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {A : Type u} [CommRing A] [IsLocalRing A] (tA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (v₁ v₂ : SchemeHomOver tA c) :
    ∃ s₀ : SchemeHomOver tA D.toBase, Nonempty ((h.poincare.pullbackAlong s₀).L ≅
      (RelEffCartierDiv.ofPoint c v₁.1 v₁.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c v₂.1 v₂.2).idealModule) := by sorry
