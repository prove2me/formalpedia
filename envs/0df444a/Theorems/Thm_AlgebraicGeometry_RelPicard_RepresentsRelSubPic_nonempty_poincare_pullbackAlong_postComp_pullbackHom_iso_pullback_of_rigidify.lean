-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_of_rigidify
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_of_rigidify
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/c87b4532-8392-52e1-a0be-53ee70f6694c
-- title:
--   Restricted Poincaré bundle at a reduced point as pullback of N
-- statement:
--   Let $R$ be a commutative ring, $c_X\colon X\to\operatorname{Spec}R$ a scheme over $R$ with a section $\varepsilon$, and $D$ a relative $\mathrm{Pic}^0$ designation for $c_X$, i.e. a scheme $P$ with a structure morphism $D.\mathrm{toBase}\colon P\to\operatorname{Spec}R$ and a zero section. Assume `hrep`: a datum `RepresentsRelSubPic` for $c_X,\varepsilon$ and the cut `algEquivZeroCut` (rigidified line bundles on $X\times_R T$ whose geometric fibres are algebraically equivalent to zero), consisting of a Poincaré bundle on $X\times_R P$ lying in the cut, the universal property classifying such bundles by morphisms to $P$, and triviality along the zero section. Let $k$ be a field and an $R$-algebra, `hreps` the corresponding datum for the base change $c_{X,k}$, the base-changed section and the base-changed designation $D_k$ (total space $P\times_{\operatorname{Spec}R}\operatorname{Spec}k$), and assume the Poincaré bundle of `hreps` is isomorphic to the bundle `BaseChange.ofR` produces from the pullback of that of `hrep` along the projection $P_k\to P$. Let $c_1\colon C_1\to\operatorname{Spec}k$ with a morphism $i_1\colon C_1\to X_k$ over $k$, a section $\varepsilon_1$ of $c_1$ with $\varepsilon_1$ followed by $i_1$ equal to the base-changed section, a designation $D_1$ and a datum `hrep₁` for $c_1,\varepsilon_1$ and its cut. Let $B$ be a commutative ring with ring maps $\rho\colon R\to B$, $\pi_k\colon B\to k$ satisfying $\mathrm{algebraMap}\,R\,k=\pi_k\circ\rho$, let $a\colon\operatorname{Spec}B\to P$ be a morphism with $D.\mathrm{toBase}\circ a=\operatorname{Spec}\rho$, and $y\colon\operatorname{Spec}k\to P_k$ a section of $(D_k).\mathrm{toBase}$ such that $y$ followed by the projection $P_k\to P$ equals $\operatorname{Spec}\pi_k$ followed by $a$. Finally let $N$ be an invertible module on $X\times_R\operatorname{Spec}B$ such that the pullback of the Poincaré bundle of `hrep` along $a$ has underlying module isomorphic to $\mathrm{rigidify}(\sigma,q,N)=N\otimes q^{*}\bigl((\sigma^{*}N)^{\vee}\bigr)$, where $\sigma=\mathrm{rigSection}$ is the section of $X\times_R\operatorname{Spec}B$ induced by $\varepsilon$ and $q$ the projection to $\operatorname{Spec}B$. Writing $\psi$ for $\operatorname{Spec}\pi_k$ regarded as a morphism over $\operatorname{Spec}\rho$, the conclusion asserts that there exists an isomorphism of modules between the underlying module of the pullback of the Poincaré bundle of `hrep₁` along $y$ followed by the restriction morphism `RepresentsRelSubPic.pullbackHom` attached to $i_1$, and the pullback of $N$ along the composite $C_1\times_k\operatorname{Spec}k\to X_k\times_k\operatorname{Spec}k\to X\times_R\operatorname{Spec}k\to X\times_R\operatorname{Spec}B$ given by `curveChange i₁.1 i₁.2 (𝟙 _)`, the comparison isomorphism `BaseChange.κ` and `baseChangeSnd cX ψ`.
--
--   This is the compatibility statement identifying, on a pointed curve $C_1$ mapping into the $k$-fibre of $X$, the line bundle classified by the image of a $k$-point $y$ under the restriction homomorphism of relative $\mathrm{Pic}^0$ with the pullback of a given invertible module $N$ on $X\times_R\operatorname{Spec}B$ along the reduction $B\to k$. It is used in the computation of the $\mathrm{Pic}^0$-class attached to a conormal bundle under Laurent-place reduction on the modular curve $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_of_rigidify.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_postComp_pullbackHom_iso_pullback_of_rigidify
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX) (hrep : RepresentsRelSubPic cX ε (algEquivZeroCut cX ε) D)
    (k : Type u) [Field k] [Algebra R k]
    (hreps : RepresentsRelSubPic (baseChange R cX k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange R cX k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR cX ε k
      (hrep.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩)).L))
    {C₁ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (i₁ : SchemeHomOver c₁ (baseChange R cX k))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)

    {B : Type u} [CommRing B] (ρ : R →+* B) (πk : B →+* k) (hAlgk : algebraMap R k = πk.comp ρ)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (hya : y.1 ≫ pullback.fst D.toBase (specMap R k) = Spec.map (CommRingCat.ofHom πk) ≫ a.1)
    (N : (pullback cX (Spec.map (CommRingCat.ofHom ρ))).Modules) (hN : Scheme.Modules.IsInvertible N)
    (isoA : (hrep.poincare.pullbackAlong a).L ≅
      Scheme.Modules.rigidify (rigSection cX (Spec.map (CommRingCat.ofHom ρ)) ε) (pullback.snd cX (Spec.map (CommRingCat.ofHom ρ))) N) :

    letI ψ : SchemeHomOver (𝟙 _ ≫ specMap R k) (Spec.map (CommRingCat.ofHom ρ)) :=
      ⟨Spec.map (CommRingCat.ofHom πk), by
        rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hAlgk]⟩
    Nonempty ((hrep₁.poincare.pullbackAlong
        (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁) y)).L ≅
      (Scheme.Modules.pullback
        (curveChange i₁.1 i₁.2 (𝟙 _) ≫ (BaseChange.κ cX k (𝟙 _)).hom ≫ baseChangeSnd cX ψ)).obj N) := by sorry
