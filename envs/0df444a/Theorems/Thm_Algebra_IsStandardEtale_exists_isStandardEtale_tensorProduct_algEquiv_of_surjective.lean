-- Prove2me | Theorems.Thm_Algebra_IsStandardEtale_exists_isStandardEtale_tensorProduct_algEquiv_of_surjective
-- name    : Algebra.IsStandardEtale.exists_isStandardEtale_tensorProduct_algEquiv_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/17542e3f-2940-52bf-a6e2-b0b869406655
-- title:
--   Standard étale algebras lift along surjections of the base
-- statement:
--   Let $C$ and $C_0$ be commutative rings with a $C$-algebra structure on $C_0$ whose structure map $C \to C_0$ is surjective, and let $S_0$ be a commutative $C_0$-algebra which is standard étale over $C_0$ in the sense of `Algebra.IsStandardEtale`, i.e. presentable as $C_0[x]_g/(f)$ with $f$ monic and $f'$ invertible in the localisation. The assertion is that there exist a type $S$, a commutative ring structure on it and a $C$-algebra structure, such that $S$ is standard étale over $C$ and the base change $C_0 \otimes_C S$ is isomorphic to $S_0$ as a $C_0$-algebra; the isomorphism is asserted only through `Nonempty`, so the statement produces existence of such an equivalence rather than a designated one. No hypothesis is imposed on the kernel of $C \to C_0$ (in particular it need not be nilpotent), and all rings here live in the base universe `Type`.
--
--   This is the classical fact that standard étale algebras, hence étale algebras locally, lift along a surjection of base rings (a ring-theoretic form of the infinitesimal lifting of étale morphisms). It is used to produce, over a closed immersion of schemes, étale opens that are pullbacks of étale schemes over the ambient base, in [`AlgebraicGeometry.Etale.exists_opens_etale_isPullback_of_isClosedImmersion`](thm.html#AlgebraicGeometry.Etale.exists_opens_etale_isPullback_of_isClosedImmersion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsStandardEtale_exists_isStandardEtale_tensorProduct_algEquiv_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.IsStandardEtale.exists_isStandardEtale_tensorProduct_algEquiv_of_surjective
    {C C₀ : Type} [CommRing C] [CommRing C₀] [Algebra C C₀] (hC : Function.Surjective (algebraMap C C₀))
    (S₀ : Type) [CommRing S₀] [Algebra C₀ S₀] [Algebra.IsStandardEtale C₀ S₀] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra C S), Algebra.IsStandardEtale C S ∧ Nonempty (C₀ ⊗[C] S ≃ₐ[C₀] S₀) := by sorry
