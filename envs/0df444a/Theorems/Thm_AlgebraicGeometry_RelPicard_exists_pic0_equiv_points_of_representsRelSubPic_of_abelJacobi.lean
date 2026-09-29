-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
-- name    : AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/f49ee66a-3217-5917-a08f-b27279caad40
-- title:
--   Represented relative Pic⁰ is abelian; Abel–Jacobi dictionary
-- statement:
--   Let $R$ be a commutative ring and $c\colon C\to\operatorname{Spec}R$ a proper morphism, smooth of relative dimension $1$ and geometrically integral, with a section $\varepsilon$ (a morphism $\operatorname{Spec}R\to C$ with $\varepsilon\circ c$ the identity). Let $D$ consist of a scheme with structure morphism `D.toBase` to $\operatorname{Spec}R$ and a section `D.zeroSection`, and let $h$ witness that $D$ represents the subfunctor of the rigidified relative Picard functor of $(c,\varepsilon)$ cut out by the condition that the line bundle be algebraically equivalent to zero on all geometric fibres: $h$ provides a Poincaré rigidified line bundle satisfying that condition, the universal property that every such bundle on a base $T\to\operatorname{Spec}R$ is the pullback of the Poincaré bundle along a unique $T$-point of $D$, and triviality of its pullback along the zero section. Assume `D.toBase` smooth, proper and geometrically connected, and let $\mathrm{aj}$ be a morphism $C\to D$ over $\operatorname{Spec}R$ with $\varepsilon$ followed by $\mathrm{aj}$ equal to `D.zeroSection`, such that for every field $K$, every $t\colon\operatorname{Spec}K\to\operatorname{Spec}R$ and every $x\colon\operatorname{Spec}K\to C$ over $t$, the pullback of the Poincaré bundle along $x$ followed by $\mathrm{aj}$ is isomorphic to the inverse ideal module of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the relative effective Cartier divisor of the section $t$ followed by $\varepsilon$. The conclusion is twofold. First, `D.toBase` is smooth, proper, has connected fibres (each set-theoretic preimage of a point of $\operatorname{Spec}R$ is connected) and admits a relative group law. Second, for every algebraically closed field $K$, every ring homomorphism $i\colon R\to K$, every field $F$ over $K$ satisfying `IsCurveOver K F` (existence of principal divisors of degree zero, residue fields of places finite over $K$, and $\Omega_{F/K}$ free of rank one), every curve model $M$ of $F/K$ and every isomorphism $e\colon M.C\to C\times_{\operatorname{Spec}R}\operatorname{Spec}K$ with $e$ followed by the second projection equal to the structure morphism of $M$, there is a bijection $\mathrm{pts}$ from $\operatorname{Pic}^0(F/K)$, the degree-zero divisors modulo principal ones, onto the set of morphisms $\operatorname{Spec}K\to D$ over $\operatorname{Spec}R$, which is additive for the relative group law that $D$ acquires from representing the group-valued functor with respect to `algEquivZeroGroupCut`, and which satisfies the following normalisation: for all $K$-points $x,s$ of $M.C$ such that $s$ followed by $e$ and the first projection equals $i$ composed with $\varepsilon$, there is a degree-zero divisor $D_v$ equal to the difference of the places of $x$ and of $s$ under the bijection between $K$-points of $M.C$ and places, with $\mathrm{pts}$ of its class given by $x$ followed by $e$, the first projection and $\mathrm{aj}$.
--
--   This is the consumer-facing dictionary for a represented relative Jacobian: it converts representability of the relative $\mathrm{Pic}^0$ functor, together with smoothness, properness and geometric connectedness of the representing scheme and an Abel–Jacobi morphism with the prescribed classifying behaviour at field-valued points, into the statement that the representing scheme is an abelian scheme over $R$ whose points over algebraically closed fields compute the degree-zero divisor class group of the corresponding function field, compatibly with the group law and with the class $[x]-[s]$. It is used in the treatment of Jacobians of modular curves and of their good-reduction models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
open AlgebraicGeometry.RelPicard

universe u v

theorem AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
    (R : Type u) [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)) :
    AbelianSchemePropertyBundle R D.toBase ∧
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : R →+* K)
        (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase →
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase,
          (∀ x y : Pic0 K F,
            pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
            s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
              Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            ∃ Dv : Divisor.degZero (K := K) (F := F),
              (Dv : Divisor K F) =
                Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
              (pts (Pic0.mk Dv)).1 =
                x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1 := by sorry
