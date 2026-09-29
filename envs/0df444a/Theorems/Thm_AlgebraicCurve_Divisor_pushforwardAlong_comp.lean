-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_comp
-- name    : AlgebraicCurve.Divisor.pushforwardAlong_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/35978d9b-0d9a-59b6-b27e-226fa3e0dc52
-- title:
--   Functoriality of divisor push-forward along composites
-- statement:
--   Let $K$ be a field and let $F$, $F'$, $F''$ be fields equipped with $K$-algebra structures. Let $\varphi \colon F \to F'$ and $\psi \colon F' \to F''$ be $K$-algebra homomorphisms, and assume that the underlying ring homomorphism of $\varphi$ is integral, that the underlying ring homomorphism of $\psi$ is integral, and that the underlying ring homomorphism of the composite $\psi \circ \varphi$ is integral (the last is a separate hypothesis because `Divisor.pushforwardAlong` takes one integrality witness for the map it is applied to). Let $D$ be a divisor of $F''$ over $K$, that is, a finitely supported function with values in $\mathbb{Z}$ on the set of places of $F''$ over $K$, a place being a valuation subring of $F''$ that contains the image of $K$, is not all of $F''$, and is a principal ideal ring. Then the push-forward of $D$ along $\psi \circ \varphi$ equals the push-forward along $\varphi$ of the push-forward of $D$ along $\psi$. Here the push-forward along an integral $K$-algebra map $\chi$ is the additive map determined on a single place $w$ by $n \mapsto n \cdot f(w \mid \chi)$ placed at the restriction of $w$ to the source, $f$ denoting the inertia degree, i.e. the degree of the corresponding residue field extension.
--
--   This is the functoriality of the proper push-forward of divisors in a tower of fields, which place by place amounts to the transitivity of restriction of places together with the multiplicativity of residue (inertia) degrees, $f(w \mid F) = f(w \mid F') \, f(w' \mid F)$. It is used in the construction of the degree-zero divisor class group machinery, being cited by [`AlgebraicCurve.Pic0.roof_package_of_surjective`](thm.html#AlgebraicCurve.Pic0.roof_package_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pushforwardAlong_comp.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pushforwardAlong_comp
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F'']
    (φ : F →ₐ[K] F') (ψ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hψφ : (ψ.comp φ).toRingHom.IsIntegral)
    (D : Divisor K F'') :
    Divisor.pushforwardAlong (ψ.comp φ) hψφ D =
      Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong ψ hψ D) := by sorry
