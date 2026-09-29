-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_eq_appTop_of_isUnit
-- name    : AlgebraicCurve.CurveModel.exists_eq_appTop_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/a135c320-0dbf-555e-afa8-5e5148ecbfa5
-- title:
--   Units of the global sections of a proper model are constants
-- statement:
--   Let $k$ be an algebraically closed field and let $M$ be a curve model of the rational function field $k(T)$ over $k$, that is: an integral scheme $C = M.C$ over the universe-$u$ base, a morphism $\mathrm{toBase} : C \to \operatorname{Spec} k$ which is proper and smooth of relative dimension $1$, a ring isomorphism $\mathrm{ffEquiv} : k(T) \xrightarrow{\sim} \mathcal{K}(C)$ onto the function field of $C$ carrying $\mathrm{algebraMap}\,k\,k(T)(a)$ to the image of $a$ under the composite of the inverse of `Scheme.ΓSpecIso`, the pullback $\mathrm{toBase}$ on global sections and the germ map at the generic point, a map $\mathrm{placeOfPoint}$ from the closed points of $C$ to the places of $k(T)$ over $k$ (a place being a valuation subring of $k(T)$ containing the image of $k$, distinct from the whole field, and a principal ideal ring) which is bijective, the requirement that for each closed point $x$ the image of the stalk $\mathcal{O}_{C,x}$ in $k(T)$, via $\mathcal{K}(C)$ and $\mathrm{ffEquiv}^{-1}$, is exactly the valuation subring of $\mathrm{placeOfPoint}\,x$, and the requirement that every finite set of points of $C$ lies in an affine open. Let $u \in \Gamma(C,\top)$ be a unit of the ring of global sections. Then there is $c \in k$ with $u$ equal to the image of $c$ under the inverse of `Scheme.ΓSpecIso` followed by $\mathrm{toBase}$ on global sections, i.e. $u$ is the constant section attached to $c$.
--
--   This is the statement that a proper smooth model of $k(T)$ has no non-constant invertible global regular functions, the scheme-theoretic form of the classical fact that the only functions regular at every place of a rational function field are the constants. It is used in the construction of the gluing datum for two projective lines, where it supplies the rigidity needed for [`AlgebraicGeometry.TwoGluedProjectiveLines.exists_nodeRatioHom`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.exists_nodeRatioHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_eq_appTop_of_isUnit.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_eq_appTop_of_isUnit
    (k : Type u) [Field k] [IsAlgClosed k] (M : CurveModel k (RatFunc k))
    (u : Γ(M.C, ⊤)) (hu : IsUnit u) :
    ∃ c : k, u = M.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by sorry
