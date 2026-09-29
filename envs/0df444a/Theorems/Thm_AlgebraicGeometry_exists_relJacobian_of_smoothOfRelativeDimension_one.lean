-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_relJacobian_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.exists_relJacobian_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/1d53824f-dad6-5adb-b310-45c9a11d3a60
-- title:
--   Relative Jacobian of a pointed smooth proper curve over a DVR
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with `IsDiscreteValuationRing`), let $C$ be a scheme and $c : C \to \operatorname{Spec} R$ a proper morphism which is smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \mathbin{\text{followed by}} c$ the identity. Then there exist a scheme $J$, a morphism $f : J \to \operatorname{Spec} R$, a relative group law $L$ on $f$ (functorial multiplication, unit and inverse on the sets of $T$-points over $\operatorname{Spec} R$, with associativity, both unit laws, left inverses, and compatibility with composition $T' \to T$), and a morphism $aj : C \to J$ with $aj$ followed by $f$ equal to $c$, such that: $f$ is smooth and proper, each fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} R$ is connected, and $f$ admits a relative group law; $L$ is commutative on $T$-points for every $T \to \operatorname{Spec} R$; $\varepsilon$ followed by $aj$ is the unit section $L.\mathrm{one}$ over the identity of $\operatorname{Spec} R$; and for every algebraically closed field $K$, every ring homomorphism $i : R \to K$, every field $F$ over $K$ satisfying `IsCurveOver K F` (every nonzero element of $F$ has a divisor of degree zero recording its orders at all places, all residue fields of places are finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$), every curve model $M$ of $F/K$ (an integral scheme $M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} K$, an isomorphism of $F$ with the function field of $M.C$ over $K$, a bijection from closed points to places matching stalks with valuation subrings, and every finite set of points contained in an affine open), and every isomorphism $e : M.C \to C \times_{\operatorname{Spec} R} \operatorname{Spec} K$ with $e$ followed by the second projection equal to $M.\mathrm{toBase}$, there is a bijection $\mathrm{pts}$ from $\operatorname{Pic}^0(F/K)$ (degree-zero divisors modulo principal ones) onto the $K$-points of $J$ over $\operatorname{Spec}\! \operatorname{map} i$, which carries addition to $L.\mathrm{mul}$, and such that for all sections $x, s$ of $M.\mathrm{toBase}$ with $s$ followed by $e$ and the first projection equal to $\operatorname{Spec}\!\operatorname{map} i$ followed by $\varepsilon$, there is a degree-zero divisor $D$ equal to the difference of the delta functions at the places attached to $x$ and to $s$, with $\mathrm{pts}$ of the class of $D$ equal to $x$ followed by $e$, the first projection, and $aj$.
--
--   This is the existence of the relative Jacobian $\operatorname{Pic}^0_{C/R,\varepsilon}$ of a pointed smooth proper curve with geometrically integral fibres over a discrete valuation ring, together with the Abel–Jacobi morphism killing the marked section and the identification of the geometric fibre's points with degree-zero divisor classes of the function field. It is the input to the statements about Galois action on $\operatorname{Pic}^0$ and about torsion in $\operatorname{Pic}^0$ under good reduction used later in the curve-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_relJacobian_of_smoothOfRelativeDimension_one.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve

universe u v

theorem AlgebraicGeometry.exists_relJacobian_of_smoothOfRelativeDimension_one
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    ∃ (J : Scheme.{u}) (f : J ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f)
      (aj : SchemeHomOver c f),
      AbelianSchemePropertyBundle R f ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        L.mul t x y = L.mul t y x) ∧
      ε.1 ≫ aj.1 = (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : R →+* K)
        (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase →
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) f,
          (∀ x y : Pic0 K F,
            pts (x + y) = L.mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
            s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
              Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            ∃ D : Divisor.degZero (K := K) (F := F),
              (D : Divisor K F) =
                Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
              (pts (Pic0.mk D)).1 =
                x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1 := by sorry
