-- Prove2me | Theorems.Thm_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed
-- name    : Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/fdb7d9b2-120d-52c1-a38c-af52591244e2
-- title:
--   Étale algebras over an algebraically closed field: point count equals dimension
-- statement:
--   Let $k$ be an algebraically closed field and let $R$ be a commutative ring equipped with a $k$-algebra structure which is étale over $k$ in Mathlib's sense (formally étale and of finite presentation over $k$). The assertion is an equality of natural numbers: the cardinality of the set $\mathrm{Hom}_{k\text{-alg}}(R,k)$ of $k$-algebra homomorphisms $R \to k$, taken as `Nat.card` (so $0$ if that set is infinite), equals the rank $\dim_k R$ of $R$ as a $k$-module, taken as `Module.finrank` (so $0$ if $R$ is not finite-dimensional). Thus an étale algebra over an algebraically closed field has exactly $\dim_k R$ points over $k$; equivalently, $\operatorname{Spec} R$ has $\dim_k R$ many $k$-points. No finiteness hypothesis on $R$ is imposed beyond what étaleness over a field already gives.
--
--   This is the standard description of étale algebras over a field in the geometric case: over an algebraically closed base, an étale algebra is a finite product of copies of $k$ and its geometric point count is its dimension. It is used in the project to count points in fibres of étale morphisms and, through [`GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf`](thm.html#GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf), in the analysis of finite flat Hopf algebras attached to Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed
    (k : Type*) [Field k] [IsAlgClosed k] (R : Type*) [CommRing R] [Algebra k R] [Algebra.Etale k R] :
    Nat.card (R →ₐ[k] k) = Module.finrank k R := by sorry
