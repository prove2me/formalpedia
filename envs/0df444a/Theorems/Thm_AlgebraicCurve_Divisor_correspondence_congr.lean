-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_correspondence_congr
-- name    : AlgebraicCurve.Divisor.correspondence_congr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/11e3dc13-e0c8-5444-9e9e-bbe826ad8168
-- title:
--   Divisor correspondences depend only on the two underlying maps
-- statement:
--   Let $K$, $F$, $F_1$ be fields with $F$ and $F_1$ algebras over $K$, and assume $F_1$ satisfies `HasPrincipalDivisors` over $K$: every $f \in F_1$ with $f \neq 0$ admits a divisor $D$ (a finitely supported $\mathbb{Z}$-valued function on the set of places of $F_1$ over $K$, a place being a valuation subring of $F_1$ containing the image of $K$, different from $F_1$ itself, and a principal ideal ring) with $D(v) = \operatorname{ord}_v(f)$ for all $v$ and $\deg D = 0$. Let $\varphi, \psi, \varphi', \psi' : F \to F_1$ be $K$-algebra maps with $\varphi = \varphi'$ and $\psi = \psi'$, let $h_\varphi, h_\psi, h_{\varphi'}, h_{\psi'}$ be witnesses that the underlying ring homomorphisms of $\varphi, \psi, \varphi', \psi'$ respectively are integral, and let $D$ be a divisor on $F$ over $K$. Then the two correspondences agree on $D$: the pushforward along $\psi$ (with witness $h_\psi$) of the pullback along $\varphi$ (with witness $h_\varphi$) of $D$ equals the pushforward along $\psi'$ (with witness $h_{\psi'}$) of the pullback along $\varphi'$ (with witness $h_{\varphi'}$) of $D$. In particular the correspondence $\psi_* \circ \varphi^*$ on divisors is unaffected by which integrality witnesses are used.
--
--   This is a congruence (rewriting) lemma for the divisorial correspondence $\psi_* \circ \varphi^*$ attached to a pair of integral $K$-algebra maps $F \to F_1$: since the construction carries proofs of integrality as arguments, identities between the maps themselves cannot be substituted directly inside it. It is used when commutation or composition identities among embeddings of function fields are transported to the associated correspondences, for instance in the commutation statements for correspondences on modular curves and in the compatibility of correspondences with the action of $K$-algebra automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_congr.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.correspondence_congr {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁] [HasPrincipalDivisors K F₁] {φ ψ φ' ψ' : F →ₐ[K] F₁} (hφeq : φ = φ') (hψeq : ψ = ψ') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (D : Divisor K F) : Divisor.correspondence φ ψ hφ hψ D = Divisor.correspondence φ' ψ' hφ' hψ' D := by sorry
