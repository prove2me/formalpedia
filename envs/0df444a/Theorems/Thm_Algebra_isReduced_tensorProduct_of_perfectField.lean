-- Prove2me | Theorems.Thm_Algebra_isReduced_tensorProduct_of_perfectField
-- name    : Algebra.isReduced_tensorProduct_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/eb74f873-7554-5ac2-9984-219f68dbba14
-- title:
--   Reduced algebras over a perfect field are geometrically reduced
-- statement:
--   Let $k$ be a field which is perfect, let $A$ be a commutative ring equipped with a $k$-algebra structure and assumed reduced (its only nilpotent element is $0$), and let $L$ be a field equipped with a $k$-algebra structure, that is, a field extension of $k$ (no finiteness or algebraicity hypothesis is imposed on $L/k$, and $A$ is not assumed of finite type). The conclusion is that the tensor product $L \otimes_k A$, as a commutative ring, is reduced. The three types $k$, $A$, $L$ live in arbitrary, possibly distinct, universes.
--
--   This is the classical statement that over a perfect base field reducedness and geometric reducedness agree, in the strong form allowing an arbitrary extension field $L$ and an arbitrary reduced $k$-algebra $A$. It is used in the project to propagate reducedness along base change, for instance to residue-field tensor products and to reducedness of pullbacks of integral models of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isReduced_tensorProduct_of_perfectField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v w

theorem Algebra.isReduced_tensorProduct_of_perfectField
    (k : Type u) [Field k] [PerfectField k] (A : Type v) [CommRing A] [Algebra k A] [IsReduced A]
    (L : Type w) [Field L] [Algebra k L] :
    IsReduced (L ⊗[k] A) := by sorry
