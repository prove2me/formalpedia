-- Prove2me | Theorems.Thm_AlgebraicCurve_finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard
-- name    : AlgebraicCurve.finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/b826eb3e-325c-53ad-9aae-23debe43188d
-- title:
--   Bombieri's Galois-closure counting identity for places
-- statement:
--   Let $K$, $F'$ and $M$ be fields with $F'$ and $M$ algebras over $K$ and $M$ an algebra over $F'$, the three structure maps forming a scalar tower, and with $M/F'$ finite and Galois. Let $\varphi : F' \to F'$ and $\psi : M \to M$ be $K$-algebra endomorphisms whose underlying ring homomorphisms are integral (every element of the target is integral over the image), and assume $\psi$ extends $\varphi$, i.e. $\psi(\iota x) = \iota(\varphi x)$ for all $x \in F'$, where $\iota : F' \to M$ is the structure map. Here a place of a field $L$ over $K$ is a valuation subring of $L$ containing the image of $K$, distinct from $L$ itself, and a principal ideal ring; pulling back along an integral $K$-algebra map sends a place to the preimage of its valuation subring, giving self-maps $\varphi^{*}$ and $\psi^{*}$ of the places of $F'$ and of $M$, and each $\tau \in \mathrm{Gal}(M/F')$ acts on places of $M$ through the semilinear automorphism $(\tau, \mathrm{id}_K)$. Assuming the fixed-point set of $\varphi^{*}$ is finite, the conclusion is twofold: for every $\tau$ the set of places $W$ of $M$ over $K$ with $\psi^{*}W = \tau \cdot W$ is finite, and $$[M : F'] \cdot \#\,\mathrm{Fix}(\varphi^{*}) = \sum_{\tau \in \mathrm{Gal}(M/F')} \#\{W : \psi^{*}W = \tau \cdot W\}.$$
--
--   This is the counting identity underlying Bombieri's Galois-closure argument (Stichtenoth, Proposition 5.2.8): fixed places of a Frobenius-type endomorphism on a base field are accounted for, with multiplicity $[M:F']$, by the places of a Galois cover fixed by the twists of the endomorphism by elements of the Galois group. It feeds the place-counting estimate [`AlgebraicCurve.exists_sub_le_sum_divisors_mul_card_places`](thm.html#AlgebraicCurve.exists_sub_le_sum_divisors_mul_card_places).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.finrank_mul_natCard_fixedPoints_restrictAlong_eq_sum_natCard
    (K F' M : Type*) [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M] [Algebra F' M]
    [IsScalarTower K F' M] [FiniteDimensional F' M] [IsGalois F' M]
    (φ : F' →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (ψ : M →ₐ[K] M) (hψ : ψ.toRingHom.IsIntegral)
    (hcomp : ∀ x : F', ψ (algebraMap F' M x) = algebraMap F' M (φ x))
    (hfin : (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφ)).Finite) :
    (∀ τ : M ≃ₐ[F'] M,
        {W : AlgebraicCurve.Place K M | W.restrictAlong ψ hψ =
            AlgebraicCurve.SemilinearAut.ofAlgAut (τ.restrictScalars K) • W}.Finite) ∧
      Module.finrank F' M *
          Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφ)) =
        ∑ τ : M ≃ₐ[F'] M,
          Nat.card {W : AlgebraicCurve.Place K M | W.restrictAlong ψ hψ =
            AlgebraicCurve.SemilinearAut.ofAlgAut (τ.restrictScalars K) • W} := by sorry
