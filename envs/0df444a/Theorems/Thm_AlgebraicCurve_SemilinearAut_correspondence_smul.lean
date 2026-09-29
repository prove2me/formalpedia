-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_correspondence_smul
-- name    : AlgebraicCurve.SemilinearAut.correspondence_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/282974e3-3cb8-5cd2-aa66-c4f5ca0a4fa6
-- title:
--   Divisor correspondences commute with intertwined semilinear automorphisms
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, and assume $F'$ has principal divisors, i.e. every nonzero $f \in F'$ admits a divisor $D$ whose coefficient at each place $v$ is $v.\mathrm{ord}(f)$ and whose degree is $0$ (places of $F$ over $K$ being valuation subrings of $F$ that contain the image of $K$, are proper, and are principal ideal rings; divisors are finitely supported $\mathbb{Z}$-valued functions on places). Let $g = (\sigma, \tau)$ be a semilinear automorphism of $F$ over $K$, that is a pair consisting of a ring automorphism of $F$ and one of $K$ compatible via the structure map, and let $g'$ be such a pair for $F'$ over $K$. Let $\varphi, \psi : F \to F'$ be $K$-algebra maps whose underlying ring homomorphisms are integral, and suppose the single automorphism $g'$ intertwines with $g$ along both, i.e. $g' \cdot \varphi(x) = \varphi(g \cdot x)$ and $g' \cdot \psi(x) = \psi(g \cdot x)$ for all $x \in F$. Then for every divisor $D$ of $F$ over $K$, the correspondence $\psi_* \circ \varphi^*$ on divisors satisfies $(\psi_* \varphi^*)(g \cdot D) = g \cdot (\psi_* \varphi^*)(D)$.
--
--   This is the equivariance of an algebraic correspondence on divisors of a curve under a semilinear automorphism intertwined along both of its legs. It is used for the induced statement on degree-zero divisor classes and, in the modular-curve and Čerednik–Drinfeld settings of the project, for the compatibility of Hecke correspondences with Galois and Frobenius actions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_correspondence_smul.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem AlgebraicCurve.SemilinearAut.correspondence_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong ψ.toRingHom g g') (D : Divisor K F) : Divisor.correspondence φ ψ hφ hψ (g • D) = g • Divisor.correspondence φ ψ hφ hψ D := by sorry
