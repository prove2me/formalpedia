-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one
-- name    : AlgebraicCurve.CurveModel.exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/9fc77781-af8e-5bf9-b2c6-855a7fe7cc3c
-- title:
--   Degree-one places give K-rational points on a curve model
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $M$ be a `CurveModel` for $L/K$: a scheme $C = M.C$ over $K$, integral, together with a morphism $M.\mathrm{toBase} : C \to \operatorname{Spec} K$ that is proper and smooth of relative dimension $1$, a ring isomorphism $M.\mathrm{ffEquiv} : L \simeq C.\mathrm{functionField}$ carrying $\mathrm{algebraMap}_{K,L}(a)$ to the image of $a$ under the map $K \to C.\mathrm{functionField}$ induced by $M.\mathrm{toBase}$ (global sections followed by the germ at the generic point), a bijection $M.\mathrm{placeOfPoint}$ from the closed points of $C$ onto the places of $L/K$ (a place being a valuation subring of $L$ containing the image of $K$, distinct from $L$ itself and a principal ideal ring), such that for each closed point $x$ the image in $L$, under $M.\mathrm{ffEquiv}^{-1}$, of the stalk $\mathcal{O}_{C,x}$ inside $C.\mathrm{functionField}$ is exactly the valuation subring of $M.\mathrm{placeOfPoint}(x)$, and such that every finite set of points of $C$ lies in one affine open. Let $x$ be a closed point of $C$ whose place has degree $1$, i.e. the residue field of the valuation subring of $M.\mathrm{placeOfPoint}(x)$ has $K$-dimension $1$. Then there is a morphism of schemes $pt : \operatorname{Spec} K \to C$ with $pt$ followed by $M.\mathrm{toBase}$ equal to the identity of $\operatorname{Spec} K$, and whose underlying map sends the closed point of $\operatorname{Spec} K$ to $x$.
--
--   This is the standard dictionary between $K$-rational points of a smooth proper model of a function field and places of degree one over $K$, in the form needed for the model: a closed point with residue degree one is cut out by a section of the structure morphism. It is used in establishing that the cusp at infinity is a rational point on a proper rational curve model of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (x : closedPoints M.C) (hx : (M.placeOfPoint x).deg = 1) :
    ∃ pt : Spec (CommRingCat.of K) ⟶ M.C,
      pt ≫ M.toBase = 𝟙 _ ∧ pt.base (IsLocalRing.closedPoint K) = x.1 := by sorry
