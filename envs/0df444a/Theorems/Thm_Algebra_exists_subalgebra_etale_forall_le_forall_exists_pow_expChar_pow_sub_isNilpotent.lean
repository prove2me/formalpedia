-- Prove2me | Theorems.Thm_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent
-- name    : Algebra.exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/dca8e6b6-94d5-51de-be5d-598d3bc1f509
-- title:
--   Maximal étale subalgebra of a finite k-algebra
-- statement:
--   Let $k$ be a field and let $A$ be a commutative ring equipped with a $k$-algebra structure making $A$ a finite $k$-module (i.e. finite-dimensional as a $k$-vector space). The assertion is the existence of a $k$-subalgebra $P \subseteq A$ with three properties: first, $P$ is étale as a $k$-algebra in the sense of Mathlib's `Algebra.Etale`; second, $P$ contains every étale $k$-subalgebra of $A$, that is, $S \le P$ for every subalgebra $S \subseteq A$ with $S$ étale over $k$, so $P$ is the unique maximal étale $k$-subalgebra; and third, every element of $A$ becomes, after raising to a suitable power of the exponential characteristic, congruent to an element of $P$ modulo nilpotents: for each $x \in A$ there are a natural number $n$ and an element $y \in P$ such that $x^{q^{n}} - y$ is nilpotent, where $q =$ `ringExpChar k` is the exponential characteristic of $k$ ($q = p$ if $\operatorname{char} k = p > 0$, and $q = 1$ if $\operatorname{char} k = 0$).
--
--   This is the existence of $\pi_0(A)$, the maximal étale (separable) $k$-subalgebra of a finite-dimensional commutative $k$-algebra, together with the statement that $A$ is radicial over it modulo nilpotents. It serves as the input for the companion criterion [`Algebra.le_of_etale_of_forall_exists_pow_expChar_pow_sub_isNilpotent`](thm.html#Algebra.le_of_etale_of_forall_exists_pow_expChar_pow_sub_isNilpotent) and for the base-change refinement [`Algebra.exists_subalgebra_etale_forall_le_forall_baseChange_le_forall_tensorProduct_le`](thm.html#Algebra.exists_subalgebra_etale_forall_le_forall_baseChange_le_forall_tensorProduct_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Algebra.exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [Module.Finite k A] :
    ∃ P : Subalgebra k A,
      Algebra.Etale k P ∧
      (∀ S : Subalgebra k A, Algebra.Etale k S → S ≤ P) ∧
      (∀ x : A, ∃ (n : ℕ) (y : A), y ∈ P ∧ IsNilpotent (x ^ ringExpChar k ^ n - y)) := by sorry
