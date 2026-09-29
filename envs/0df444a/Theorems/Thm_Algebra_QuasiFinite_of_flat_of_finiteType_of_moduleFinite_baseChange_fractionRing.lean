-- Prove2me | Theorems.Thm_Algebra_QuasiFinite_of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing
-- name    : Algebra.QuasiFinite.of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/55bb2f70-be98-5019-9a24-ca92d6d2f54c
-- title:
--   Quasi-finiteness from flatness and a module-finite generic fibre
-- statement:
--   Let $R$ be a commutative ring which is a domain and a principal ideal ring, and let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$ (i.e. the localisation of $R$ at its nonzero elements). Let $S$ be a commutative $R$-algebra which is of finite type over $R$ (finitely generated as an $R$-algebra) and flat as an $R$-module, and assume that the generic fibre $K \otimes_R S$ is finite as a $K$-module, that is, a finite-dimensional $K$-vector space. The conclusion is that the algebra $R \to S$ is quasi-finite in Mathlib's sense: for every prime ideal $P$ of $R$, the fibre of $S$ at $P$ is a finite module over the residue field of $P$; equivalently, $\kappa(P) \otimes_R S$ is a finite-dimensional $\kappa(P)$-vector space for all $P \in \operatorname{Spec} R$. No Noetherian hypothesis beyond the principal ideal ring assumption on $R$ is imposed, and the three universes of $R$, $K$ and $S$ are unconstrained.
--
--   This is the standard criterion that a flat algebra of finite type over a principal ideal domain whose generic fibre is module-finite has module-finite fibres at every prime, i.e. is quasi-finite. It is used in the verification that a certain Hopf-algebra quotient is Hopf–Galois with faithfully flat and finite-type kernel, where quasi-finiteness over the base is needed at all primes rather than only at the generic one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_QuasiFinite_of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Algebra.QuasiFinite.of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type w) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [Module.Flat R S]
    [Module.Finite K (K ⊗[R] S)] :
    Algebra.QuasiFinite R S := by sorry
