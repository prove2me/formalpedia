-- Prove2me | Theorems.Thm_AlgebraicClosure_exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime
-- name    : AlgebraicClosure.exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/4eaff0e7-afbb-58b4-8506-4d35f844b2f0
-- title:
--   Mod-L cyclotomic character takes value ℓ at Frobenius
-- statement:
--   Let $L$ be a natural number, nonzero. The assertion is the existence of a monoid homomorphism $\chi$ from the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` to the unit group $(\mathbb{Z}/L)^\times$, together with an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, such that three things hold: first, $F$ is finite-dimensional over $\mathbb{Q}$; second, $\chi$ is trivial on the subgroup of automorphisms fixing $F$ pointwise, that is, $\chi\tau = 1$ whenever $\tau x = x$ for all $x \in F$; third, for every prime number $\ell$ with $\ell \nmid L$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ such that the image of $\ell$ is a non-unit of $A$ (the `LiesOverPrime` condition), and every automorphism $\sigma$ which is a Frobenius at $A$ for the exponent $\ell$ — meaning that $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and the resulting action of $\sigma$ on the residue field of $A$ is $x \mapsto x^{\ell}$ — one has $\chi\sigma =$ `ZMod.unitOfCoprime ℓ _`, the unit of $\mathbb{Z}/L$ determined by $\ell$ together with its coprimality to $L$, i.e. the class of $\ell$ modulo $L$.
--
--   This packages the mod-$L$ cyclotomic character of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$: it is unramified outside the finite level $F = \mathbb{Q}(\mu_L)$ and sends a Frobenius at a prime $\ell \nmid L$ to $\ell \bmod L$. It is used in the form needed for the Eichler–Shimura relation with a diamond-operator twist, being cited by [`GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius`](thm.html#GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicClosure_exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem AlgebraicClosure.exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime
    (L : ℕ) [NeZero L] :
    ∃ (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ)
      (F : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ F ∧
      (∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, τ x = x) → χ τ = 1) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L)
        (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          χ σ = ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL) := by sorry
