-- Prove2me | Theorems.Thm_Field_nonempty_ringHom_complex_of_countable
-- name    : Field.nonempty_ringHom_complex_of_countable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/b0d9247e-2403-5333-8974-53b3fcd60c6b
-- title:
--   Countable fields of characteristic zero embed into ℂ
-- statement:
--   Let $K$ be a type in an arbitrary universe, equipped with a field structure, of characteristic zero, and countable (in the sense that its underlying type admits an injection into $\mathbb{N}$, i.e. is finite or countably infinite). The assertion is that the type $K \to+^* \mathbb{C}$ of ring homomorphisms from $K$ to the field of complex numbers is nonempty: there exists at least one ring homomorphism $K \to \mathbb{C}$. Since $K$ is a field, any such homomorphism is automatically injective, so the conclusion is an embedding of $K$ as a subfield of $\mathbb{C}$; the statement itself, however, asserts only the existence of a ring homomorphism, with no further properties and no compatibility with prescribed data. Note that the conclusion is a statement of nonemptiness (a `Prop`), not a chosen map, and that the universe of $K$ is unrestricted, so the cardinality comparison involved is a cross-universe one.
--
--   This is the set-theoretic half of the Lefschetz principle for countable fields of characteristic zero. It is used to transfer a statement about $j$-invariants and modular polynomials from an arbitrary countable characteristic-zero base field to $\mathbb{C}$, in the proof of [`WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`](thm.html#WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Field_nonempty_ringHom_complex_of_countable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Field.nonempty_ringHom_complex_of_countable
    (K : Type u) [Field K] [CharZero K] [Countable K] : Nonempty (K →+* ℂ) := by sorry
