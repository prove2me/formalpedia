-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_correspondence_comm_of_exchange
-- name    : AlgebraicCurve.Divisor.correspondence_comm_of_exchange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/b44f958f-3c10-5c5c-b2d7-59ee6c4c3585
-- title:
--   Exchanged legs force a divisor correspondence to be self-transpose
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ $K$-algebras, and assume $F'$ has the property `HasPrincipalDivisors`: every nonzero $f \in F'$ admits a divisor $D$ on $F'$ (an element of the free abelian group on the places of $F'$ over $K$, a place being a valuation subring of $F'$ containing the image of $K$, distinct from $F'$ itself and a principal ideal ring) with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ and $\deg D = 0$. Let $\varphi, \psi \colon F \to F'$ be $K$-algebra maps whose underlying ring homomorphisms are integral, so that the correspondence $\psi_* \circ \varphi^\ast =$ `Divisor.correspondence φ ψ hφ hψ`, an endomorphism of the group of divisors on $F$, is defined. Let $g \colon F' \to F'$ be a $K$-algebra endomorphism which is integral and surjective and which exchanges the two legs, i.e. $g \circ \varphi = \psi$ and $g \circ \psi = \varphi$. Then the two correspondences obtained from the ordered pairs $(\varphi,\psi)$ and $(\psi,\varphi)$ coincide as additive endomorphisms of the divisor group of $F$: $\psi_* \circ \varphi^\ast = \varphi_* \circ \psi^\ast$.
--
--   This is the divisor-theoretic form of the classical observation that a correspondence whose two projections are interchanged by an automorphism of the covering object equals its own transpose, as for the Hecke correspondence on modular curves exchanged by an Atkin–Lehner involution. It is used in the construction of Hecke data on modular curves, in [`ModularCurve.SSLevelDatum.exists_heckeRowSums_and_adjointPair_laws`](thm.html#ModularCurve.SSLevelDatum.exists_heckeRowSums_and_adjointPair_laws).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_comm_of_exchange.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Divisor.correspondence_comm_of_exchange {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (g : F' →ₐ[K] F') (hg : g.toRingHom.IsIntegral) (hgs : Function.Surjective g) (h1 : g.comp φ = ψ) (h2 : g.comp ψ = φ) : AlgebraicCurve.Divisor.correspondence φ ψ hφ hψ = AlgebraicCurve.Divisor.correspondence ψ φ hψ hφ := by sorry
