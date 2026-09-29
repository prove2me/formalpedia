-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_inertiaDegAlong_comp
-- name    : AlgebraicCurve.Place.inertiaDegAlong_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/c9a09ece-3a42-5346-8fc5-a227abeaca40
-- title:
--   Multiplicativity of the inertia degree in a tower
-- statement:
--   Let $K$ be a field and let $F$, $F'$, $F''$ be fields equipped with $K$-algebra structures, and let $\varphi \colon F \to F'$ and $\chi \colon F' \to F''$ be $K$-algebra homomorphisms whose underlying ring homomorphisms are integral, with integrality of the composite $\chi \circ \varphi$ assumed as a separate hypothesis. Let $W$ be a place of $F''$ over $K$, that is, a valuation subring of $F''$ containing the image of $K$, different from $F''$ itself, and whose ring is a principal ideal ring. For an integral $K$-algebra map $\psi$, the place obtained by restricting $W$ along $\psi$ is the preimage valuation subring of $W$ under $\psi$, and the inertia degree of $W$ along $\psi$ is the $\mathbb{N}$-valued rank $\operatorname{finrank}$ of the residue field of $W$ as a module over the residue field of that restricted place (so the value is $0$ when this residue extension is infinite). The conclusion is that the inertia degree of $W$ along $\chi \circ \varphi$ equals the product of the inertia degree of $W$ along $\chi$ and the inertia degree, along $\varphi$, of the restriction of $W$ along $\chi$. No finiteness hypothesis is imposed, so the identity also covers the case in which all three degrees are $0$.
--
--   This is the classical multiplicativity of the residue (inertia) degree $f$ in a tower of function fields, here for places presented as principal valuation subrings and with inertia degrees defined as residue-field ranks. It is used in the theory of divisor push-forward along correspondences, notably for the composition law for push-forwards and in the fundamental-identity statements summing $e \cdot f$ over a bifibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_inertiaDegAlong_comp.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.inertiaDegAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') : W.inertiaDegAlong (χ.comp φ) hχφ = W.inertiaDegAlong χ hχ * (W.restrictAlong χ hχ).inertiaDegAlong φ hφ := by sorry
