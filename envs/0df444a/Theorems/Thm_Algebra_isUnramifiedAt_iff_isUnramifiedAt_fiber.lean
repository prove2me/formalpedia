-- Prove2me | Theorems.Thm_Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber
-- name    : Algebra.isUnramifiedAt_iff_isUnramifiedAt_fiber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/31f14e0d-bcad-52d7-b913-b34d4efaebf2
-- title:
--   Unramifiedness at a prime is detected on the fibre
-- statement:
--   Let $R$ and $A$ be commutative rings with $A$ an $R$-algebra that is essentially of finite type. Let $P$ be a prime ideal of $R$ and $Q$ a prime ideal of $A$ lying over $P$, and let $Q'$ be a prime ideal of the fibre $P.\mathrm{Fiber}\,A = \kappa(P) \otimes_R A$, where $\kappa(P)$ denotes the residue field `P.ResidueField` of $R$ at $P$. Assume that $Q$ is the contraction of $Q'$ along the ring homomorphism $A \to \kappa(P) \otimes_R A$ given by `Algebra.TensorProduct.includeRight`, i.e. $Q = Q' \cap A$. The theorem asserts the equivalence: $A$ is unramified over $R$ at $Q$ (in the sense of `Algebra.IsUnramifiedAt R Q`, membership of the point $Q$ in the unramified locus of $A$ over $R$) if and only if the fibre $\kappa(P) \otimes_R A$ is unramified over $\kappa(P)$ at $Q'$. Both directions are contained in the statement; no finiteness or flatness hypothesis beyond essential finite type is imposed, and $Q'$ is not assumed to be the unique prime contracting to $Q$.
--
--   This is the standard fibrewise criterion for unramifiedness (as in EGA IV 17.4.1): unramifiedness of $A/R$ at a prime depends only on the fibre over the image prime, so questions about ramification at $Q$ reduce to a question about a finite-type algebra over the field $\kappa(P)$. It is used in the project to obtain the trace-dual characterisation of unramifiedness for free, integrally closed extensions, [`Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed`](thm.html#Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.isUnramifiedAt_iff_isUnramifiedAt_fiber
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.EssFiniteType R A]
    (P : Ideal R) [P.IsPrime] (Q : Ideal A) [Q.IsPrime] [Q.LiesOver P]
    (Q' : Ideal (P.Fiber A)) [Q'.IsPrime]
    (hQ' : Q = Q'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    Algebra.IsUnramifiedAt R Q ↔ Algebra.IsUnramifiedAt P.ResidueField Q' := by sorry
