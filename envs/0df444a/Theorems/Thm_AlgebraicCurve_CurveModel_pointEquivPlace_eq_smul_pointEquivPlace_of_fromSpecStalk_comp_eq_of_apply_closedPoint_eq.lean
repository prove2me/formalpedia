-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq
-- name    : AlgebraicCurve.CurveModel.pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/47e263ae-17c9-5597-b148-b6a10cf48630
-- title:
--   Semilinear transport of places under a curve-model automorphism
-- statement:
--   Let $K$ be an algebraically closed field and $L$ a field equipped with a $K$-algebra structure, and let $M$ be a curve model of $L$ over $K$: a scheme $C = M.C$ together with a morphism $M.\mathrm{toBase} : C \to \operatorname{Spec} K$ which is integral, proper and smooth of relative dimension $1$, a ring isomorphism $\mathrm{ff} = M.\mathrm{ffEquiv} : L \xrightarrow{\sim} K(C)$ onto the function field which carries $\operatorname{algebraMap} K L$ to the map $K \to K(C)$ induced by $M.\mathrm{toBase}$, a bijection $\mathrm{placeOfPoint}$ from the closed points of $C$ onto the places of $L$ over $K$ (valuation subrings of $L$ containing the image of $K$, proper in $L$, and principal ideal rings) matching each stalk with the corresponding valuation subring through $\mathrm{ff}^{-1}$, and the condition that every finite set of points of $C$ lies in an affine open. Let $g$ be a semilinear automorphism, that is a pair consisting of a ring automorphism $g_L$ of $L$ and a ring automorphism $g_K$ of $K$ with $g_L(a) = g_K(a)$ for $a$ in the image of $K$, and let $\theta : C \to C$ be an isomorphism of schemes, not assumed to lie over $\operatorname{Spec} K$. Assume that on the generic point $\theta$ induces $g_L^{-1}$ through $\mathrm{ff}$, in the sense that $\mathrm{fromSpecStalk}$ at the generic point followed by $\theta$ equals $\operatorname{Spec}$ of the ring homomorphism $\mathrm{ff} \circ g_L^{-1} \circ \mathrm{ff}^{-1}$ of $K(C)$ followed by $\mathrm{fromSpecStalk}$ at the generic point. Let $x, x'$ be $K$-points of $C$, that is morphisms $\operatorname{Spec} K \to C$ splitting $M.\mathrm{toBase}$, and suppose that the image of the closed point of $\operatorname{Spec} K$ under $x'$ is the image under $\theta$ of its image under $x$. Then the place attached to $x'$ by $M.\mathrm{pointEquivPlace}$ equals $g$ acting on the place attached to $x$, the action being by transport of the valuation subring along $g_L$.
--
--   This is the semilinear version of the statement that an automorphism of a smooth proper curve model acts on places compatibly with its action on $K$-points, the $K$-linearity of $\theta$ being replaced by the requirement that $\theta$ induce a prescribed semilinear automorphism $g^{-1}$ of the function field. It is used in the analysis of explicit models of the modular curve $X_1(p)$, where the arithmetic Galois action, Galois twists and diamond automorphisms are compared with their effect on places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v in

theorem AlgebraicCurve.CurveModel.pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (g : SemilinearAut K L)
    (θ : M.C ⟶ M.C) [IsIso θ]

    (hθgen : M.C.fromSpecStalk (genericPoint M.C) ≫ θ =
      Spec.map (CommRingCat.ofHom
        (M.ffEquiv.toRingHom.comp ((SemilinearAut.toRingAut g).symm.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C))
    (x x' : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (hxx' : x'.1.base (IsLocalRing.closedPoint K) = θ.base (x.1.base (IsLocalRing.closedPoint K))) :
    M.pointEquivPlace x' = g • M.pointEquivPlace x := by sorry
