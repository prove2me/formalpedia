-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/3c4d0a8f-24be-5122-9830-10b6f4fba612
-- title:
--   Geometric fibre of a smooth proper curve as a model of its function field
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme and let $c : C \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically integral; let $k$ be an algebraically closed field and $s : \operatorname{Spec} k \to \operatorname{Spec} R$ a morphism. Write $C_s = C \times_{\operatorname{Spec} R} \operatorname{Spec} k$, and equip its function field (the stalk of the structure sheaf at the generic point) with the $k$-algebra structure induced by the second projection $\mathrm{pr}_2 : C_s \to \operatorname{Spec} k$ via `baseToFunctionField`, i.e. global sections pulled back along $\mathrm{pr}_2$ and then taken as germs at the generic point. The assertion is that, for this $k$-algebra structure, there exist: an instance of `IsCurveOver k` on $k(C_s)$, that is, every nonzero $f$ admits a divisor recording its orders at all places and of degree $0$, every place has residue field finite over $k$, and $\Omega_{k(C_s)/k}$ is free of rank $1$; an instance of `Algebra.EssFiniteType k` on $k(C_s)$; a `CurveModel` $M$ for $k(C_s)/k$ (an integral scheme $M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, with a ring isomorphism $M.\mathrm{ffEquiv} : k(C_s) \cong k(M.C)$ over $k$, a bijection between the closed points of $M.C$ and the places of $k(C_s)/k$ matching stalks with valuation subrings, and every finite set of points contained in an affine open); and an isomorphism of schemes $e : M.C \cong C_s$ with $e$ followed by $\mathrm{pr}_2$ equal to $M.\mathrm{toBase}$, such that for every open $U \subseteq C_s$ with both $U$ and $e^{-1}U$ nonempty and every $t \in \Gamma(C_s, U)$ one has $M.\mathrm{ffEquiv}^{-1}\bigl(\operatorname{germ}_{M.C}(e^{-1}U, e^{*}t)\bigr) = \operatorname{germ}_{C_s}(U, t)$.
--
--   This realises the geometric fibre of a smooth proper relative curve as a model, in the project's sense, of its own function field over the algebraically closed base field, with the identification of function fields pinned so that germs of sections transport correctly. It feeds the comparison of curve models and reductions used in the geometric input to the modularity argument, and is cited in the construction of constant reductions and of models compatible with a given function-field isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra AlgebraicCurve

theorem AlgebraicGeometry.SmoothProperCurve.exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    letI : Algebra k (pullback c s).functionField := (baseToFunctionField (pullback.snd c s)).toAlgebra
    ∃ (_ : IsCurveOver k (pullback c s).functionField) (_ : Algebra.EssFiniteType k (pullback c s).functionField)
      (M : CurveModel k (pullback c s).functionField) (e : M.C ≅ pullback c s),
      e.hom ≫ pullback.snd c s = M.toBase ∧
      ∀ (U : (pullback c s).Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (e.hom ⁻¹ᵁ U))]
        (t : Γ(pullback c s, U)),
        M.ffEquiv.symm (M.C.germToFunctionField (e.hom ⁻¹ᵁ U) ((e.hom.app U).hom t)) =
          (pullback c s).germToFunctionField U t := by sorry
