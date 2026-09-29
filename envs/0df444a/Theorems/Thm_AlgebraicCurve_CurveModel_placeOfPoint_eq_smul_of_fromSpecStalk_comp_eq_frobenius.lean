-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius
-- name    : AlgebraicCurve.CurveModel.placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/a2ecab66-a87f-510f-a995-f48bbe5e33dd
-- title:
--   A Frobenius endomorphism of a curve model twists places by g
-- statement:
--   Let $K$ be a field, $p$ a prime, and assume $K$ has characteristic $p$. Let $L$ be a field with a $K$-algebra structure and let $M$ be a `CurveModel K L`: a scheme $M.C$, integral, with a proper morphism $M.toBase$ to $\operatorname{Spec} K$ that is smooth of relative dimension $1$, a ring isomorphism $M.ffEquiv : L \simeq M.C.functionField$ compatible with the structure maps from $K$, a bijection $M.placeOfPoint$ from the closed points of $M.C$ onto the places of $L/K$ (valuation subrings of $L$ containing the image of $K$, different from $L$, and principal ideal rings) which sends a point to the valuation subring that is the image of its local ring in the function field, and the property that every finite set of points of $M.C$ lies in an affine open. Let $g$ be an element of `SemilinearAut K L`, i.e. a pair consisting of a ring automorphism of $L$ and a ring automorphism of $K$ that are compatible with $\operatorname{algebraMap} K L$. Let $\Phi : L \to L$ be a $K$-algebra homomorphism with $\Phi(f) = (g^{-1}\cdot f)^p$ for all $f \in L$, and assume `FiniteAlong K Φ`, that is, $L$ is a finite module over itself via $\Phi$. Let $\theta : M.C \to M.C$ be a morphism of schemes whose restriction to the generic point is $\operatorname{Spec}$ of $\Phi$ read through $M.ffEquiv$: the canonical map from the spectrum of the stalk at the generic point followed by $\theta$ equals $\operatorname{Spec}$ of $M.ffEquiv \circ \Phi \circ M.ffEquiv^{-1}$ followed by that canonical map. Then for every closed point $y$ of $M.C$ the point $\theta(y)$ is again closed, and $M.placeOfPoint(\theta(y)) = g \cdot M.placeOfPoint(y)$, the pointwise translate of the valuation subring by the automorphism component of $g$.
--
--   This identifies the action on closed points, hence on places of $L/K$, of an endomorphism of a smooth proper curve model whose effect on the function field is the $K$-linear (relative) Frobenius $f \mapsto (g^{-1}f)^p$ attached to a semilinear automorphism $g$: it acts on places by the twist $v \mapsto g\cdot v$. It is used in the study of Frobenius-type endomorphisms of modular curve models, in the computation of the place attached to a fibre map at level $\Gamma$ and in the comparison of $q$-expansion places under raising a chart to the $p$-th power.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius
    {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)
    (g : SemilinearAut K L)
    (Φ : L →ₐ[K] L) (hΦ : ∀ f : L, Φ f = (g⁻¹ • f) ^ p) (hfin : FiniteAlong K Φ)
    (θ : M.C ⟶ M.C)
    (hθgen : M.C.fromSpecStalk (genericPoint M.C) ≫ θ =
      Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (Φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C))
    (y : closedPoints M.C) :
    ∃ h : θ.base y.1 ∈ closedPoints M.C, M.placeOfPoint ⟨θ.base y.1, h⟩ = g • M.placeOfPoint y := by sorry
