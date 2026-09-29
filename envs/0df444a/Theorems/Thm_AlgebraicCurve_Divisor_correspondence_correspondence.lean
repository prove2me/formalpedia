-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_correspondence_correspondence
-- name    : AlgebraicCurve.Divisor.correspondence_correspondence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/bfe16466-5880-55a1-8fa8-d4e02e1c0fa6
-- title:
--   Composite of two divisor correspondences through a roof
-- statement:
--   Let $K$ be a field and let $F$, $F_1$, $F_2$, $Z$ be field extensions of $K$, with $F_1$, $F_2$, $Z$ satisfying `HasPrincipalDivisors` over $K$, i.e. every nonzero element $f$ of the field has a divisor $D$ on the places over $K$ (valuation subrings containing $\operatorname{im}(K)$, proper, and principal ideal rings) with $D(v)=\operatorname{ord}_v(f)$ at every place $v$ and $\deg D=0$. Let $\varphi,\psi\colon F\to F_1$ and $\varphi',\psi'\colon F\to F_2$ and $u\colon F_1\to Z$, $u'\colon F_2\to Z$ be $K$-algebra maps, and assume each of $\varphi$, $\psi$, $\varphi'$, $\psi'$, $u$, $u'$, as well as the composites $u'\circ\varphi'$ and $u\circ\psi$, is integral. Here $\varphi^{*}$ (`pullbackAlong`) and $\psi_{*}$ (`pushforwardAlong`) denote the pull-back and push-forward of divisors for the algebra structure induced by the map, and $\mathrm{corr}(\varphi,\psi)=\psi_{*}\circ\varphi^{*}$ on $\operatorname{Div}(K,F)=\bigl(\text{places of }F/K\bigr)\to_{\mathrm{f}}\mathbb{Z}$. Assume the exchange identity $\varphi^{*}\circ\psi'_{*}=u_{*}\circ u'^{*}$ as maps $\operatorname{Div}(K,F_2)\to\operatorname{Div}(K,F_1)$. Then for every divisor $D$ on $F$, $\mathrm{corr}(\varphi,\psi)\bigl(\mathrm{corr}(\varphi',\psi')(D)\bigr)=\mathrm{corr}(u'\circ\varphi',\,u\circ\psi)(D)$.
--
--   This is the composition law for correspondences of function fields in the divisor-group formulation: two correspondences with common source $F$ compose to the single correspondence whose legs factor through the roof $Z$, provided the middle square satisfies the stated exchange identity (classically a consequence of that square being Cartesian together with the multiplicativity of ramification and residue degrees in towers). It is used for the Hecke correspondences on modular curves, where it yields the composition and commutation relations of Hecke divisor operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_correspondence.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.correspondence_correspondence {K F F₁ F₂ Z : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] [HasPrincipalDivisors K Z] (φ ψ : F →ₐ[K] F₁) (φ' ψ' : F →ₐ[K] F₂) (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral) (huφ' : (u'.comp φ').toRingHom.IsIntegral) (huψ : (u.comp ψ).toRingHom.IsIntegral) (hex : ∀ D : Divisor K F₂, Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D) = Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D)) (D : Divisor K F) : Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) = Divisor.correspondence (u'.comp φ') (u.comp ψ) huφ' huψ D := by sorry
