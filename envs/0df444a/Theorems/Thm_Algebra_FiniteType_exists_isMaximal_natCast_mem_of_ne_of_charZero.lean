-- Prove2me | Theorems.Thm_Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero
-- name    : Algebra.FiniteType.exists_isMaximal_natCast_mem_of_ne_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/c19f1446-7638-586d-9ec0-96e3949f324f
-- title:
--   Two residue characteristics for a finitely generated ℤ-algebra domain
-- statement:
--   Let $A$ be a commutative ring which is an integral domain of characteristic zero and which is of finite type as a $\mathbb{Z}$-algebra (that is, $A$ is a quotient of a polynomial ring over $\mathbb{Z}$ in finitely many variables). The assertion is that there exist natural numbers $p_1, p_2$ and ideals $\mathfrak{m}_1, \mathfrak{m}_2$ of $A$ such that $p_1$ and $p_2$ are prime, $p_1 \neq p_2$, both $\mathfrak{m}_1$ and $\mathfrak{m}_2$ are maximal ideals of $A$, and the image of $p_1$ under the canonical map $\mathbb{N} \to A$ lies in $\mathfrak{m}_1$ while that of $p_2$ lies in $\mathfrak{m}_2$. Thus $A$ has two maximal ideals whose residue fields have distinct characteristics; the statement asserts only the membership relations $p_i \in \mathfrak{m}_i$, and not the finiteness of the residue fields, although that finiteness is what makes the statement true.
--
--   This is the commutative-algebra ingredient of Selberg's lemma: a finitely generated $\mathbb{Z}$-algebra that is a domain of characteristic zero admits maximal ideals of at least two distinct residue characteristics, which is what allows two different primes to be used simultaneously when constructing a torsion-free finite-index subgroup. It is used in the proof of [`Matrix.GeneralLinearGroup.exists_normal_relIndex_ne_zero_forall_isOfFinOrder_imp_eq_one_of_fg`](thm.html#Matrix.GeneralLinearGroup.exists_normal_relIndex_ne_zero_forall_isOfFinOrder_imp_eq_one_of_fg), the Selberg-type statement for general linear groups over finitely generated rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem Algebra.FiniteType.exists_isMaximal_natCast_mem_of_ne_of_charZero
    (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] :
    ∃ (p₁ p₂ : ℕ) (𝔪₁ 𝔪₂ : Ideal A), p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧ 𝔪₁.IsMaximal ∧ 𝔪₂.IsMaximal ∧
      (p₁ : A) ∈ 𝔪₁ ∧ (p₂ : A) ∈ 𝔪₂ := by sorry
