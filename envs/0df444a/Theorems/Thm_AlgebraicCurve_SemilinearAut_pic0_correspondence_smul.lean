-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul
-- name    : AlgebraicCurve.SemilinearAut.pic0_correspondence_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/4d797403-137e-5107-af8c-59abd2cb7bef
-- title:
--   Correspondences on Pic⁰ commute with intertwined semilinear automorphisms
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$, let $g$ be an element of `SemilinearAut K F`, i.e. a pair consisting of a ring automorphism of $F$ and one of $K$ compatible with the structure map $K \to F$, and let $g'$ be such a pair for $F'/K$; assume `HasPrincipalDivisors K F'`, so that each nonzero $f \in F'$ has a divisor whose value at every place $v$ of $F'/K$ is $\operatorname{ord}_v f$ and whose degree is $0$. Let $\varphi, \psi : F \to F'$ be $K$-algebra maps whose underlying ring homomorphisms are integral, with hypotheses: `FundamentalIdentityAlong` for $\varphi$ (the fundamental identity for $F'$ over $F$ with $F$ acting through $\varphi$), finiteness of $F'$ as an $F$-module through $\psi$, and the pushforward norm formula for divisors along $\psi$. Assume further that $g'$ intertwines $g$ along both legs: $g' \cdot \varphi(x) = \varphi(g \cdot x)$ and $g' \cdot \psi(x) = \psi(g \cdot x)$ for all $x \in F$. Then for every class $c$ in $\mathrm{Pic}^0(F/K)$, the degree-zero divisor classes modulo principal divisors, the correspondence $\mathrm{Pic}^0$-endomorphism given by pullback along $\varphi$ followed by pushforward along $\psi$ satisfies $T(g \cdot c) = g \cdot T(c)$.
--
--   This is the equivariance of an algebraic correspondence on a curve, realised as pushforward after pullback on degree-zero divisor classes, under a semilinear automorphism of the function field; for modular and Shimura curves it yields the commutation of Hecke operators with the Galois action on the Jacobian once the two degeneracy maps are intertwined. It is used in the construction of Hecke towers on Shimura curve models and in the corresponding statements for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul.lean

import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem AlgebraicCurve.SemilinearAut.pic0_correspondence_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong ψ.toRingHom g g') (c : Pic0 K F) : Pic0.correspondence φ ψ hφ hψ hFI hfin hN (g • c) = g • Pic0.correspondence φ ψ hφ hψ hFI hfin hN c := by sorry
