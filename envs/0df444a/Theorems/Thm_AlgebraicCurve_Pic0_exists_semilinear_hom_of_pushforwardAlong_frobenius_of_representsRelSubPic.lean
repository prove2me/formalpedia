-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic
-- name    : AlgebraicCurve.Pic0.exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/d2699b24-dde1-553f-b3f1-075a61f73758
-- title:
--   Frobenius push-forward realised by a semilinear Jacobian morphism
-- statement:
--   Let $k$ be a finite field with $q = \#k$ elements, $K$ an algebraically closed field, and $F_0$, $F$ fields with $F_0$ a $k$-algebra, $F$ a $K$-algebra and an $F_0$-algebra, such that $F_0/k$ and $F/K$ are curves in the sense of `IsCurveOver` (every nonzero function has a divisor, of degree $0$; all residue fields of places are finite over the base field; and the module of Kähler differentials is free of rank one). Assume $F_0$ is the intermediate field generated over $k$ by some finite subset, and $F$ is generated over $K$ by the image of $F_0$. Let $\varphi : F \to F$ be a $K$-algebra endomorphism whose underlying ring homomorphism is integral and which acts on the image of $F_0$ by $x \mapsto x^{q}$. Let $M$ be a `CurveModel` of $F/K$: an integral scheme $M.C$ with a proper, smooth of relative dimension one morphism to $\operatorname{Spec} K$, an identification of $F$ with its function field over $K$, and a bijection between its closed points and the places of $F/K$, compatible with valuation rings, together with the property that every finite set of points lies in an affine open. Let $s$ be a $K$-point of $M.C$, that is a section of $M.\mathrm{toBase}$. Let $D$ consist of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} K$ and a zero section, and let $h$ witness that $D$ represents, via a rigidified Poincaré bundle on the fibre product of $M.C$ with $D.P$, the subfunctor of $s$-rigidified relative line bundles on $M.C$ cut out by the condition that the restriction to every geometric fibre is algebraically equivalent to zero. Let $\mathrm{aj}$ be a morphism $M.C \to D.P$ over $\operatorname{Spec} K$ with $s$ followed by $\mathrm{aj}$ equal to the zero section, such that for every field $K'$, every $t : \operatorname{Spec} K' \to \operatorname{Spec} K$ and every $K'$-point $x$ of $M.C$ over $t$, the pullback of the Poincaré bundle along $x$ followed by $\mathrm{aj}$ is isomorphic to the tensor product of the inverse ideal module of the relative effective Cartier divisor attached to the point $x$ with the ideal module of the one attached to $t$ followed by $s$. Finally let $\mathrm{pts}$ be a bijection from $\mathrm{Pic}^0(F/K)$, the quotient of degree-zero divisors by principal ones, onto the $K$-points of $D.P$, which is additive for the relative group law on $D.P$ coming from $h$ and the group structure on the algebraic-equivalence-to-zero condition, and which sends, for every $K$-point $x$ of $M.C$, the class of a degree-zero divisor equal to $[\,\text{place of } x\,] - [\,\text{place of } s\,]$ to $x$ followed by $\mathrm{aj}$. Then there is a ring homomorphism $\sigma : K \to K$ with $\sigma(c) = c^{q}$ for all $c$, and a morphism $N_B : D.P \to D.P$ with $N_B$ followed by $D.\mathrm{toBase}$ followed by $\operatorname{Spec}(\sigma)$ equal to $D.\mathrm{toBase}$, such that for every degree-zero divisor $Dv$ on $F/K$ the $K$-point attached by $\mathrm{pts}$ to the class of the push-forward of $Dv$ along $\varphi$ equals $\operatorname{Spec}(\sigma)$ followed by $\mathrm{pts}$ of the class of $Dv$ followed by $N_B$.
--
--   This is the semilinear half of the description of the Frobenius endomorphism of a Jacobian: the push-forward of divisor classes along the relative $q$-power Frobenius of the function field is induced by a morphism from the Jacobian to its $\sigma$-twist, where $\sigma$ is the $q$-power map of the algebraically closed base field. It is used in the proof that the induced endomorphism acts trivially on the cotangent space at the origin, namely in [`AlgebraicCurve.Pic0.map_maximalIdeal_le_sq_of_pushforwardAlong_frobenius_of_representsRelSubPic`](thm.html#AlgebraicCurve.Pic0.map_maximalIdeal_le_sq_of_pushforwardAlong_frobenius_of_representsRelSubPic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian AlgebraicCurve

universe u v

theorem AlgebraicCurve.Pic0.exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic
    (k : Type*) (K : Type u) (F₀ : Type*) (F : Type v) [Field k] [Finite k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (M : CurveModel K F)
    (s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (D : RelativePic0Designation K M.toBase)
    (h : RepresentsRelSubPic M.toBase s (algEquivZeroCut M.toBase s) D)
    (aj : SchemeHomOver M.toBase D.toBase) (hajs : s.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K' : Type u) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
        (x : SchemeHomOver t M.toBase),
      Nonempty ((h.poincare.pullbackAlong
          ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M.toBase (t ≫ s.1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) s.2).trans (Category.comp_id t)))).idealModule))
    (pts : Pic0 K F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase)
    (hadd : ∀ x y : Pic0 K F, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h).mul _ (pts x) (pts y))
    (hnorm : ∀ x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      ∃ Dv : Divisor.degZero (K := K) (F := F),
        (Dv : Divisor K F) =
          Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ aj.1) :
    ∃ σ : K →+* K, (∀ c : K, σ c = c ^ Nat.card k) ∧
      ∃ NB : D.P ⟶ D.P, NB ≫ D.toBase ≫ Spec.map (CommRingCat.ofHom σ) = D.toBase ∧
        ∀ Dv : Divisor.degZero (K := K) (F := F),
          (pts (Pic0.mk ⟨Divisor.pushforwardAlong φ hφi Dv,
              Divisor.pushforwardAlong_mem_degZero φ hφi Dv.2⟩)).1 =
            Spec.map (CommRingCat.ofHom σ) ≫ (pts (Pic0.mk Dv)).1 ≫ NB := by sorry
