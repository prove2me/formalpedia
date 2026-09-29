-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_map_maximalIdeal_le_sq_of_pushforwardAlong_frobenius_of_representsRelSubPic
-- name    : AlgebraicCurve.Pic0.map_maximalIdeal_le_sq_of_pushforwardAlong_frobenius_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/1f1958c7-1b63-5b49-8dcc-a639868f6d31
-- title:
--   Vanishing differential of the Frobenius endomorphism of a Jacobian
-- statement:
--   Let $k$ be a finite field, $K$ an algebraically closed field, and $F_0/k$, $F/K$ field extensions with $F$ an $F_0$-algebra, both $F_0/k$ and $F/K$ satisfying `IsCurveOver` (principal divisors of degree zero exist, every place has residue field finite over the base, and the module of Kähler differentials is free of rank one). Assume $F_0$ is generated over $k$ by a finite set, $F$ is generated over $K$ by the image of $F_0$, and $\varphi : F \to F$ is a $K$-algebra endomorphism which is integral as a ring homomorphism and acts on the image of $F_0$ by $x \mapsto x^{\#k}$. Let $M$ be a `CurveModel` of $F/K$ (an integral scheme $M.C$, proper and smooth of relative dimension one over $\operatorname{Spec} K$, with $F$ identified with its function field and its closed points identified with the places of $F/K$), and $s$ a section of $M.\mathrm{toBase}$. Let $D$ be a relative $\mathrm{Pic}^0$ designation for $M.\mathrm{toBase}$ (a scheme $D.P$ over $\operatorname{Spec} K$ with a zero section) and $h$ a witness that $D$ represents the subfunctor of the $s$-rigidified relative Picard functor of $M.\mathrm{toBase}$ cut out by the condition that the line bundle be algebraically equivalent to zero on every geometric fibre: $h$ provides a Poincaré bundle on $D.P$ satisfying this condition, the universal property that every such rigidified bundle over a base $t$ is the pullback of the Poincaré bundle along a unique $T$-point of $D.P$ over $\operatorname{Spec} K$, and triviality of its pullback along the zero section. Let $aj$ be a morphism $M.C \to D.P$ over $\operatorname{Spec} K$ with $s$ followed by $aj$ the zero section and such that, for every field $K'$, every $t : \operatorname{Spec} K' \to \operatorname{Spec} K$ and every point $x$ of $M.C$ over $t$, the pullback of the Poincaré bundle along $x$ followed by $aj$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the relative effective Cartier divisor of the point $t$ followed by $s$. Let $pts$ be a bijection from $\mathrm{Pic}^0$ of $F/K$ (degree-zero divisors modulo principal ones) to the $K$-points of $D.P$, additive for the relative group law attached to $h$ via the group-theoretic cut `algEquivZeroGroupCut`, and such that for every $K$-point $x$ of $M.C$ some degree-zero divisor equal to $[\,$place of $x\,] - [\,$place of $s\,]$ has $pts$ of its class equal to $x$ followed by $aj$. Finally let $N$ be an endomorphism of $D.P$ over $\operatorname{Spec} K$ which is a homomorphism for the relative group law on $T$-points for every $T$ and every structure morphism $t$, and which induces the push-forward of divisor classes along $\varphi$: for every degree-zero divisor $Dv$, $pts$ of the class of $\varphi_* Dv$ equals $pts$ of the class of $Dv$ followed by $N$. Then for every point $x$ of $D.P$, the image under the stalk map of $N$ at $x$ of the maximal ideal of the stalk at $N(x)$ is contained in the square of the maximal ideal of the stalk at $x$.
--
--   This is the statement that the Frobenius endomorphism of the Jacobian, realised here as push-forward of divisor classes along the relative $q$-Frobenius of the function field, has vanishing differential at every point of the Jacobian, in the strong scheme-theoretic form that the comorphism carries the maximal ideal into the square of the maximal ideal. It feeds the computation of the characteristic polynomial of this endomorphism on torsion, used in [`AlgebraicCurve.Pic0.exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius`](thm.html#AlgebraicCurve.Pic0.exists_monic_natCard_ker_aeval_eq_resultant_map_of_pushforwardAlong_frobenius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_map_maximalIdeal_le_sq_of_pushforwardAlong_frobenius_of_representsRelSubPic.lean

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

theorem AlgebraicCurve.Pic0.map_maximalIdeal_le_sq_of_pushforwardAlong_frobenius_of_representsRelSubPic
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
        (pts (Pic0.mk Dv)).1 = x.1 ≫ aj.1)
    (N : SchemeHomOver D.toBase D.toBase)
    (hNhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h).mul t x y) N =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h).mul t
          (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N))
    (hN : ∀ Dv : Divisor.degZero (K := K) (F := F),
      (pts (Pic0.mk ⟨Divisor.pushforwardAlong φ hφi Dv,
          Divisor.pushforwardAlong_mem_degZero φ hφi Dv.2⟩)).1 = (pts (Pic0.mk Dv)).1 ≫ N.1)
    (x : D.P) :
    (IsLocalRing.maximalIdeal (D.P.presheaf.stalk (N.1.base x))).map (N.1.stalkMap x).hom ≤
      IsLocalRing.maximalIdeal (D.P.presheaf.stalk x) ^ 2 := by sorry
