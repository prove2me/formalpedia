-- Prove2me | Theorems.Thm_Algebra_IsIntegral_injective_of_injective_algebraMap
-- name    : Algebra.IsIntegral.injective_of_injective_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/3e4faec0-ed85-593d-bfd0-cb79e653d88d
-- title:
--   Integral A-algebra maps into a domain over A are injective
-- statement:
--   Let $A$, $B$, $C$ be commutative rings with $B$ and $C$ integral domains, and let $B$ and $C$ both carry $A$-algebra structures, the algebra $B$ over $A$ being integral (every element of $B$ satisfies a monic polynomial over $A$). Assume that the structure map $\mathrm{algebraMap}\colon A \to C$ is injective, and let $\varphi\colon B \to C$ be a homomorphism of $A$-algebras. The conclusion is that $\varphi$ is injective as a map of sets. Note that no finiteness is assumed of $B$ over $A$, only integrality, and that injectivity of $A \to C$ is assumed rather than injectivity of $A \to B$; the hypothesis that $C$ is a domain enters through the primality of $\ker\varphi$, and the hypothesis that $B$ is a domain together with integrality through the incomparability statement used.
--
--   This is the incomparability property of integral extensions in the form usually applied: a prime of an integral extension of $A$ by a domain which contracts to the zero ideal of $A$ is itself zero. It is used in the proof of the criterion [`IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete`](thm.html#IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete), to see that a comparison map out of a domain presented as an integral algebra is injective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsIntegral_injective_of_injective_algebraMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.IsIntegral.injective_of_injective_algebraMap
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C] [Algebra.IsIntegral A B]
    (hinj : Function.Injective (algebraMap A C)) (φ : B →ₐ[A] C) :
    Function.Injective φ := by sorry
