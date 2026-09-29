-- Prove2me | Theorems.Thm_AlgebraicClosure_exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one
-- name    : AlgebraicClosure.exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/42c77540-436d-5170-8716-cccb028a04eb
-- title:
--   Cyclotomic character is trivial mod pⁿ on a finite level
-- statement:
--   Let $p$ be a prime and $n$ a natural number. The assertion is the existence of an intermediate field $F$ of the extension $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, where $\overline{\mathbb{Q}}$ is Mathlib's algebraic closure of $\mathbb{Q}$, such that $F$ is finite-dimensional over $\mathbb{Q}$ and such that, for every $\mathbb{Q}$-algebra automorphism $\tau$ of $\overline{\mathbb{Q}}$ which fixes every element of $F$, the image of the $p$-adic cyclotomic character value $\mathrm{cyclotomicCharacter}\,\overline{\mathbb{Q}}\,p\,\tau \in \mathbb{Z}_p^{\times}$, viewed in $\mathbb{Z}_p$ and reduced by `PadicInt.toZModPow n` to $\mathbb{Z}/p^n$, equals $1$. Here $\tau$ enters the character through its underlying ring equivalence `τ.toRingEquiv`. Thus the conclusion is the congruence $\varepsilon_p(\tau) \equiv 1 \pmod{p^n}$ for all $\tau$ in the subgroup of the absolute Galois group of $\mathbb{Q}$ fixing $F$ pointwise; no continuity or closedness of the fixing subgroup is asserted, and the field $F$ is produced only as a finite-dimensional intermediate field, its identification with $\mathbb{Q}(\mu_{p^n})$ not being part of the statement.
--
--   This is the finite-level form of the continuity of the $p$-adic cyclotomic character: its reduction modulo $p^n$ is trivial on the Galois group over a suitable number field, namely the $p^n$-th cyclotomic field. It is used in the study of adic Galois representations, where it supplies the open subgroup on which the determinant-type cyclotomic factor becomes trivial modulo $p^n$; it is cited by [`GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius`](thm.html#GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicClosure_exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem AlgebraicClosure.exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, τ x = x) →
        PadicInt.toZModPow n ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by sorry
