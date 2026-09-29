-- Prove2me | Theorems.Thm_Algebra_PointDerivations_finite_and_finrank_eq_mul_of_surjective_of_ker
-- name    : Algebra.PointDerivations.finite_and_finrank_eq_mul_of_surjective_of_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/0230744f-de81-5a80-b952-48f8c5b8d824
-- title:
--   Point derivations as Hom_k(Ω, M): finiteness and dimension
-- statement:
--   Let $k$ be a field and $A$ a commutative $k$-algebra, and let $\mathrm{ev} : A \to k$ be a ring homomorphism whose composition with the structure map $k \to A$ is the identity of $k$; write $\mathfrak m = \ker(\mathrm{ev})$, regarded as a $k$-submodule of $A$ by restriction of scalars. Let $\Omega$ be a $k$-vector space that is finite as a $k$-module, and let $\pi : \mathfrak m \to \Omega$ be a surjective $k$-linear map such that, for $x \in \mathfrak m$, $\pi(x) = 0$ holds if and only if $x$ lies in the ideal $\mathfrak m^2$ (so $\pi$ presents $\Omega$ abstractly as $\mathfrak m/\mathfrak m^2$). Let $M$ be a further $k$-vector space finite as a $k$-module. The assertion is that the $k$-submodule $\mathrm{PointDerivations}_k(A,\mathrm{ev};M)$ of $\mathrm{Hom}_k(A,M)$ — by definition the set of $k$-linear maps $D : A \to M$ satisfying $D(ab) = \mathrm{ev}(a)\cdot D(b) + \mathrm{ev}(b)\cdot D(a)$ for all $a,b \in A$ — is finite as a $k$-module, and that its $k$-dimension equals $\dim_k \Omega \cdot \dim_k M$.
--
--   This is the standard identification of the tangent-vector-valued point derivations at the $k$-point $\mathrm{ev}$ with $\mathrm{Hom}_k(\mathfrak m/\mathfrak m^2, M)$, here phrased so that the cotangent space is supplied abstractly as any $k$-linear surjection from $\mathfrak m$ with kernel $\mathfrak m^2$, together with the resulting dimension count. It is used in the construction of formal coordinates on bare deformation functors, via [`GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_PointDerivations_finite_and_finrank_eq_mul_of_surjective_of_ker.lean

import Mathlib
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w w'

theorem Algebra.PointDerivations.finite_and_finrank_eq_mul_of_surjective_of_ker
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] (ev : A →+* k)
    (hev : ev.comp (algebraMap k A) = RingHom.id k)
    (Ω : Type w) [AddCommGroup Ω] [Module k Ω] [Module.Finite k Ω]
    (π : ↥((RingHom.ker ev).restrictScalars k) →ₗ[k] Ω) (hπ : Function.Surjective π)
    (hπker : ∀ x : ↥((RingHom.ker ev).restrictScalars k), π x = 0 ↔ (x : A) ∈ (RingHom.ker ev) ^ 2)
    (M : Type w') [AddCommGroup M] [Module k M] [Module.Finite k M] :
    Module.Finite k ↥(Algebra.PointDerivations k A ev M) ∧
      Module.finrank k ↥(Algebra.PointDerivations k A ev M) = Module.finrank k Ω * Module.finrank k M := by sorry
