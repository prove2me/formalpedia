-- Prove2me | Theorems.Thm_Algebra_FiniteType_exists_isMaximal_and_finite_quotient_of_int
-- name    : Algebra.FiniteType.exists_isMaximal_and_finite_quotient_of_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/6c4c0ea2-ea0a-51f4-a348-5b967472bd8e
-- title:
--   Finitely generated ℤ-algebras have a finite residue field
-- statement:
--   Let $R$ be a commutative ring in the zeroth universe, equipped with a $\mathbb Z$-algebra structure, assumed nontrivial (so $0 \neq 1$) and of finite type over $\mathbb Z$, i.e. generated as a $\mathbb Z$-algebra by finitely many elements. The conclusion asserts the existence of an ideal $\mathfrak m \subseteq R$ which is maximal and whose quotient ring $R/\mathfrak m$ is finite. Thus the assertion is the existential one: at least one maximal ideal of $R$ has finite residue field. (In fact every maximal ideal of such an $R$ has finite residue field, but that stronger statement is not what is formalised here.)
--
--   This is the arithmetic form of the Nullstellensatz over $\mathbb Z$: a field of finite type as a $\mathbb Z$-algebra is finite, combined with the existence of a maximal ideal in a nonzero ring. It is used in the part of the argument concerning polarised abelian schemes, where a finite residue field is needed to pass from a finite-type base to a base over a finite field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FiniteType_exists_isMaximal_and_finite_quotient_of_int.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.FiniteType.exists_isMaximal_and_finite_quotient_of_int
    (R : Type) [CommRing R] [Algebra ℤ R] [Nontrivial R] [Algebra.FiniteType ℤ R] :
    ∃ 𝔪 : Ideal R, 𝔪.IsMaximal ∧ Finite (R ⧸ 𝔪) := by sorry
