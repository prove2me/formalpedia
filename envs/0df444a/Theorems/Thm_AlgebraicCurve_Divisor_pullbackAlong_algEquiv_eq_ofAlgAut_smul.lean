-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul
-- name    : AlgebraicCurve.Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/2330b831-d5c7-52a6-964f-80e52930d7c1
-- title:
--   Pull-back along a K-automorphism is the semilinear action
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume [`AlgebraicCurve.HasPrincipalDivisors K F`](def/AlgebraicCurve_DivisorClassGroup.html#L217), i.e. every nonzero $f \in F$ admits a divisor whose coefficient at each place $v$ is $\operatorname{ord}_v f$ and whose degree is $0$; here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, and a divisor is a finitely supported function from places to $\mathbb{Z}$. Let $\sigma$ be a $K$-algebra automorphism of $F$, let $h\sigma$ assert that the ring homomorphism underlying the $K$-algebra map $\sigma\colon F \to F$ is integral, and let $D$ be a divisor of $F/K$. The conclusion is that the pull-back of $D$ along $\sigma$, formed by equipping $F$ with the $F$-algebra structure coming from $\sigma$ and applying [`AlgebraicCurve.Divisor.pullback`](def/AlgebraicCurve_DivisorPushPull.html#L549), agrees with $g \bullet D$, where $g =$ [`AlgebraicCurve.SemilinearAut.ofAlgAut`](def/AlgebraicCurve_BaseChangeGalois.html#L76) $\sigma$ is the element $(\sigma, 1)$ of the group of pairs $(\tau_F, \tau_K)$ of ring automorphisms compatible with $K \to F$, acting on divisors through its action on places.
--
--   This is the identification of the conorm (pull-back) map along an isomorphism of function fields with the transport of divisors by that isomorphism. It is used to convert pull-backs along automorphisms into the semilinear action on divisors, and hence on divisor classes, in the degeneracy and Hecke relations on the Jacobians of modular curves, being cited in the comparison of $\varphi^*\varphi_*$ with a sum of Galois translates and in the relations for Hecke, Atkin–Lehner and diamond operators on $J_H$ and $J_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.HasPrincipalDivisors K F]
    (σ : F ≃ₐ[K] F) (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral) (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.Divisor.pullbackAlong (σ : F →ₐ[K] F) hσ D = AlgebraicCurve.SemilinearAut.ofAlgAut σ • D := by sorry
