-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/e97926cc-390a-58a0-8c5f-45160b56aad8
-- title:
--   Constant genus of geometric fibres via a two-chart cover
-- statement:
--   Let $R$ be a local Noetherian commutative ring, let $C$ be a scheme and $c \colon C \to \operatorname{Spec} R$ a morphism that is proper, smooth of relative dimension $1$ and geometrically integral, and let $\mathcal V$ be a `TwoAffineOpenCover` of $C$, i.e. two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Then there is a natural number $g$ with the following property. Let $k$ be an algebraically closed field, $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$ any morphism, $L$ a field with a $k$-algebra structure, and $M$ a `CurveModel` for $L/k$: a scheme $M.C$ with an integral structure, a proper morphism $M.\mathrm{toBase} \colon M.C \to \operatorname{Spec} k$ smooth of relative dimension $1$, a ring isomorphism $L \cong$ the function field of $M.C$ compatible with the structure map on $k$, a bijection from the closed points of $M.C$ onto the places of $L/k$ (valuation subrings of $L$, proper, containing $k$, with principal ideals) matching stalks with valuation subrings, and the property that every finite set of points lies in one affine open. Let $e \colon M.C \cong \operatorname{pullback} c\, s$ be an isomorphism with $e$ followed by $\mathrm{pullback.snd}$ equal to $M.\mathrm{toBase}$, let $K_c$ be a divisor of $L/k$ (a finitely supported $\mathbb Z$-valued function on places) and $g'$ a natural number. If $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ for every divisor $D$, where $\ell$ is the $k$-dimension of the Riemann–Roch space and $\deg$ weights each place by its residue degree, then $g' = g$.
--
--   This is the constancy of the genus in a smooth proper family of geometrically integral curves over a local Noetherian base, in the form: any number $g'$ certified by a Riemann–Roch formula on the function field of a geometric fibre equals one fixed invariant $g$ of the family, computed from a two-chart affine cover. It is used in the construction and fibrewise analysis of the relative Picard scheme, for instance in the computations of the ranks of $H^0$ and $H^1$ of the unit fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra AlgebraicCurve

theorem AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] (𝒱 : C.TwoAffineOpenCover) :
    ∃ g : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by sorry
