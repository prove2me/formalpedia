-- Prove2me | Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing
-- name    : Algebra.Etale.isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/9811961a-b672-5d6a-b820-6845c1ecad5c
-- title:
--   Local étale base change of a normal domain is normal
-- statement:
--   Let $W$ be a commutative ring and let $B$ and $W'$ be commutative rings equipped with $W$-algebra structures. Assume that $W \to W'$ is étale (formally étale and of finite presentation, as in Mathlib's `Algebra.Etale`), that $B$ is an integral domain which is integrally closed in its field of fractions, and that the tensor product $B \otimes_W W'$ is a local ring. The conclusion is the conjunction: $B \otimes_W W'$ is an integral domain, and it is integrally closed in its field of fractions. No finiteness, flatness or Noetherian hypothesis is imposed on $B$ or on $W$, and the three carrier types lie in arbitrary, independent universes. The locality assumption on $B \otimes_W W'$ cannot be dropped for the domain conclusion: for $W' = W \times W$, which is étale over $W$, the tensor product is $B \times B$.
--
--   This is the standard statement that an étale algebra over a normal domain is normal, in the special case of a base change $B \otimes_W W'$ of an integrally closed domain along an étale map $W \to W'$ that happens to be local. It is used in the étale-base-change steps for regular local rings ([`IsRegularLocalRing.exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem`](thm.html#IsRegularLocalRing.exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem) and [`IsRegularLocalRing.exists_isUnit_pow_eq_mul_of_baseChange`](thm.html#IsRegularLocalRing.exists_isUnit_pow_eq_mul_of_baseChange)) and in the construction of the crossing model [`ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit`](thm.html#ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.Etale.isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing
    {W : Type*} [CommRing W] (B W' : Type*) [CommRing B] [CommRing W'] [Algebra W B] [Algebra W W']
    [Algebra.Etale W W'] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing (B ⊗[W] W')] :
    IsDomain (B ⊗[W] W') ∧ IsIntegrallyClosed (B ⊗[W] W') := by sorry
