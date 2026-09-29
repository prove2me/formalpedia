-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
-- name    : AlgebraicGeometry.RelPicard.exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/179bbc38-6168-53d6-8a13-df1bd53435ce
-- title:
--   Group law, Abel–Jacobi map and points of a represented relative Pic⁰
-- statement:
--   Let $R$ be a commutative ring and $c\colon C\to\operatorname{Spec}R$ a proper morphism, smooth of relative dimension $1$ and geometrically integral, with $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec}R\to C$ composing with $c$ to the identity). Let $D$ consist of a scheme $P$, a structure morphism $D.\mathrm{toBase}\colon P\to\operatorname{Spec}R$ and a section $D.\mathrm{zeroSection}$ of it, and assume $D$ represents the subfunctor of rigidified line bundles on $C$ cut out by fibrewise algebraic equivalence to zero: a Poincaré rigidified bundle on $C\times_R P$ satisfying that condition, universality of its pullbacks among such bundles over any base $t\colon T\to\operatorname{Spec}R$, and triviality of its pullback along the zero section. Assume further $D.\mathrm{toBase}$ is smooth, proper and geometrically connected. Then there exist a relative group law $L$ on $D.\mathrm{toBase}$ (functorial multiplication, unit, inverse on $T$-points over $\operatorname{Spec}R$, with the group axioms and naturality in $T$) and a morphism $\mathrm{aj}\colon C\to P$ over $\operatorname{Spec}R$ such that: $D.\mathrm{toBase}$ is smooth and proper with connected fibres and carries a relative group law; each $L.\mathrm{mul}$ is commutative; the unit on $\operatorname{Spec}R$-points is $D.\mathrm{zeroSection}$; $\varepsilon$ followed by $\mathrm{aj}$ is $D.\mathrm{zeroSection}$; and for every algebraically closed field $K$, ring homomorphism $i\colon R\to K$, field $F$ over $K$ satisfying `IsCurveOver K F` (principal divisors, finite residue extensions at all places, and $\Omega_{F/K}$ free of rank one), every curve model $M$ of $F/K$ and every isomorphism $e\colon M.C\to C\times_{\operatorname{Spec}R}\operatorname{Spec}K$ over $\operatorname{Spec}K$, there is a bijection $\mathrm{pts}$ from $\mathrm{Pic}^0(F/K)$ to the $K$-points of $P$ over $\operatorname{Spec}R$ carrying addition to $L.\mathrm{mul}$, and such that for all $K$-points $x,s$ of $M.C$ with $s$ mapping under $e$ followed by the first projection to the base change of $\varepsilon$, there is a degree-zero divisor equal to $[\,\text{place of }x\,]-[\,\text{place of }s\,]$ whose class has $\mathrm{pts}$-image the morphism $x$ followed by $e$, the first projection and $\mathrm{aj}$.
--
--   This is the dictionary attached to a represented relative $\mathrm{Pic}^0$ of a pointed smooth proper curve: the representing object is an abelian scheme for the group law induced by tensor product of rigidified line bundles, the Abel–Jacobi morphism sends a point to the class of $\mathcal{O}([x]-[\varepsilon])$, and on geometric fibres its points are identified with degree-zero divisor classes of the function field. It is used in the construction of the relative Jacobian, [`AlgebraicGeometry.exists_relJacobian_of_smoothOfRelativeDimension_one_of_finiteMapData`](thm.html#AlgebraicGeometry.exists_relJacobian_of_smoothOfRelativeDimension_one_of_finiteMapData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicCurve

universe u v

theorem AlgebraicGeometry.RelPicard.exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
    (R : Type u) [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase) :
    ∃ (L : RelativeGroupLaw R D.toBase) (aj : SchemeHomOver c D.toBase),
      AbelianSchemePropertyBundle R D.toBase ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
        L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = D.zeroSection ∧
      ε.1 ≫ aj.1 = D.zeroSection ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : R →+* K)
        (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase →
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase,
          (∀ x y : Pic0 K F,
            pts (x + y) = L.mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
            s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
              Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            ∃ Dv : Divisor.degZero (K := K) (F := F),
              (Dv : Divisor K F) =
                Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
              (pts (Pic0.mk Dv)).1 =
                x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1 := by sorry
