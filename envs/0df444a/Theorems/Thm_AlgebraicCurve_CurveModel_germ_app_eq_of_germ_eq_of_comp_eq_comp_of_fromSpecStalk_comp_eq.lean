-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_germ_app_eq_of_germ_eq_of_comp_eq_comp_of_fromSpecStalk_comp_eq
-- name    : AlgebraicCurve.CurveModel.germ_app_eq_of_germ_eq_of_comp_eq_comp_of_fromSpecStalk_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/85c1f674-cf13-50a4-82bc-5100f7bcae8a
-- title:
--   Transport of a pinned function-field embedding along a lift
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $M$ be a `CurveModel K L`: a scheme $M.C$ with a proper, smooth of relative dimension $1$ morphism to $\operatorname{Spec} K$, integral, together with a ring isomorphism $M.\mathrm{ffEquiv} : L \cong M.C.\mathrm{functionField}$ compatible with the structure map on $K$, a bijection between the closed points of $M.C$ and the places of $L/K$ matching stalks with valuation subrings, and the property that every finite set of points lies in one affine open. Let $Y$ be an integral scheme, $\varphi : Y \to M.C$ a morphism sending the generic point of $Y$ to the generic point of $M.C$, and $j : L \to Y.\mathrm{functionField}$ a ring homomorphism pinned to $\varphi$ in the sense that for every $x \in L$, every open $U \subseteq M.C$ containing the generic point with generic point of $Y$ in $\varphi^{-1}U$, and every section $s$ over $U$ whose germ at the generic point is $M.\mathrm{ffEquiv}(x)$, the germ of $\varphi^{*}s$ at the generic point of $Y$ is $j(x)$. Let $V$ be a $K$-algebra automorphism of $L$ and $h : M.C \to M.C$ a morphism with $M.C.\mathrm{fromSpecStalk}(\eta)$ followed by $h$ equal to $\operatorname{Spec}$ of the ring map $M.\mathrm{ffEquiv} \circ V \circ M.\mathrm{ffEquiv}^{-1}$ followed by $M.C.\mathrm{fromSpecStalk}(\eta)$, where $\eta$ is the generic point of $M.C$. Let $a : Y \to Y$ fix the generic point of $Y$ and satisfy $a$ followed by $\varphi$ equal to $\varphi$ followed by $h$. Then $a$ transports $j$ by $V$: for every $x \in L$, every open $U \subseteq Y$ containing the generic point with generic point also in $a^{-1}U$, and every section $s$ over $U$ whose germ at the generic point is $j(x)$, the germ of $a^{*}s$ at the generic point is $j(V x)$.
--
--   This is the transport step for a pinned embedding of the function field: an automorphism of the base model acting on $L$ by $V$, together with a lift to $Y$ compatible with $\varphi$, forces the lift to act on the pinned copy of $L$ inside the function field of $Y$ by the same $V$. It is used in the Čerednik–Drinfel'd part of the development, to establish Atkin–Lehner equivariance of the pinned function-field embedding on the relevant covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_germ_app_eq_of_germ_eq_of_comp_eq_comp_of_fromSpecStalk_comp_eq.lean

import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve Opposite

theorem AlgebraicCurve.CurveModel.germ_app_eq_of_germ_eq_of_comp_eq_comp_of_fromSpecStalk_comp_eq
    {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L] (M : CurveModel K L)
    {Y : Scheme.{u}} [IsIntegral Y] (φ : Y ⟶ M.C) (hφ : φ.base (genericPoint Y) = genericPoint M.C)
    (j : L →+* Y.functionField)
    (hpin : ∀ (x : L) (U : M.C.Opens) (hU : genericPoint M.C ∈ U) (hU' : genericPoint Y ∈ φ ⁻¹ᵁ U)
        (sec : M.C.presheaf.obj (op U)),
        (M.C.presheaf.germ U (genericPoint M.C) hU).hom sec = M.ffEquiv x →
        (Y.presheaf.germ (φ ⁻¹ᵁ U) (genericPoint Y) hU').hom ((φ.app U).hom sec) = j x)
    (V : L ≃ₐ[K] L) (h : M.C ⟶ M.C)
    (hh : M.C.fromSpecStalk (genericPoint M.C) ≫ h =
      Spec.map (CommRingCat.ofHom
        (M.ffEquiv.toRingHom.comp ((V : L →ₐ[K] L).toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C))
    (a : Y ⟶ Y) (ha₀ : a.base (genericPoint Y) = genericPoint Y) (ha : a ≫ φ = φ ≫ h) :
    ∀ (x : L) (U : Y.Opens) (hU : genericPoint Y ∈ U) (hU' : genericPoint Y ∈ a ⁻¹ᵁ U)
      (sec : Y.presheaf.obj (op U)),
      (Y.presheaf.germ U (genericPoint Y) hU).hom sec = j x →
      (Y.presheaf.germ (a ⁻¹ᵁ U) (genericPoint Y) hU').hom ((a.app U).hom sec) = j (V x) := by sorry
