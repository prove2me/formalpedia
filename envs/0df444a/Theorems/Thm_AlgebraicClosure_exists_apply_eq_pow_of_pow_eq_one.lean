-- Prove2me | Theorems.Thm_AlgebraicClosure_exists_apply_eq_pow_of_pow_eq_one
-- name    : AlgebraicClosure.exists_apply_eq_pow_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/418bdb7b-a880-56a1-a51b-4ec3f62a3e22
-- title:
--   Automorphisms of ℚ̄ act on n-th roots of unity by a power
-- statement:
--   Let $n$ be a natural number with $n \neq 0$, and let $\sigma$ be an automorphism of the field `AlgebraicClosure ℚ` as an algebra over $\mathbb{Q}$, i.e. an element of `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`. The assertion is that there exists a natural number $a$ such that for every $\mu$ in `AlgebraicClosure ℚ` satisfying $\mu^n = 1$ one has $\sigma(\mu) = \mu^a$. Thus a single exponent $a$, depending only on $n$ and $\sigma$, computes the action of $\sigma$ on all $n$-th roots of unity simultaneously; no claim is made that $a$ is unique, that it is prime to $n$, or that the assignment $\sigma \mapsto a$ is multiplicative, and $a$ is given as a natural number rather than as a unit modulo $n$. The hypothesis $n \neq 0$ is needed both to make the group of $n$-th roots of unity finite and to exclude $\mu = 0$.
--
--   This is the elementary statement that the Galois action on $n$-th roots of unity in $\overline{\mathbb{Q}}$ is by raising to a power, i.e. the existence of an exponent realising the mod $n$ cyclotomic character. It serves as the exponent-existence input for the cyclotomic-determinant and descent arguments elsewhere in the development, such as the surjectivity statements for bialgebra maps from monoid algebras and the Weil-pairing computations on the modular-curve side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicClosure_exists_apply_eq_pow_of_pow_eq_one.lean

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicClosure.exists_apply_eq_pow_of_pow_eq_one (n : ℕ) (hn : n ≠ 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ a : ℕ, ∀ μ : AlgebraicClosure ℚ, μ ^ n = 1 → σ μ = μ ^ a := by sorry
