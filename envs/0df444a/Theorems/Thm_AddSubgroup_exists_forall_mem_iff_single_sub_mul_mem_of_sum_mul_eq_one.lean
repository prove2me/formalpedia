-- Prove2me | Theorems.Thm_AddSubgroup_exists_forall_mem_iff_single_sub_mul_mem_of_sum_mul_eq_one
-- name    : AddSubgroup.exists_forall_mem_iff_single_sub_mul_mem_of_sum_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/b7fe63a2-8cc7-58d7-9589-bc583eb49a58
-- title:
--   Unipotent splitting of an 𝒪-stable subgroup of D²
-- statement:
--   Let $D$ be a ring, let $O \subseteq D$ be a subset, and let $M$ be an additive subgroup of $D^2 = (\mathrm{Fin}\,2 \to D)$ which is stable under coordinatewise right multiplication by $O$: for every $m \in M$ and every $o \in O$ the vector $i \mapsto m_i \, o$ again lies in $M$. Let $\iota$ be a type, $t$ a finite subset of $\iota$, and $x, y : \iota \to D$ two families such that (i) for each $k \in t$ the element $x_k$ occurs as the second coordinate of some member of $M$, i.e. there is $m \in M$ with $m_1 = x_k$; (ii) for each $k \in t$ and every $m \in M$ one has $y_k \, m_1 \in O$, that is $y_k$ multiplies the second projection of $M$ into $O$; and (iii) $\sum_{k \in t} x_k \, y_k = 1$. Then there exists $u \in D$ such that for every $v \in D^2$, $v \in M$ if and only if both the vector with first coordinate $v_0 - u\,v_1$ and second coordinate $0$ lies in $M$, and $v_1$ is the second coordinate of some member of $M$.
--
--   The conclusion is the explicit unipotent normal form $M = \begin{pmatrix} 1 & u \\ 0 & 1\end{pmatrix}(I_1 \times I_2)$ for a right $O$-stable subgroup $M \subseteq D^2$ whose second projection $I_2$ is invertible in the weak sense encoded by the data $x_k, y_k$, with $I_1 = \{a : (a,0) \in M\}$; it is the concrete form of the splitting of a module over the projective ideal onto which it surjects. It is used in the analysis of lattices over maximal orders in quaternion algebras, through [`QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mem_iff_forall_mulVec_mem`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mem_iff_forall_mulVec_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddSubgroup_exists_forall_mem_iff_single_sub_mul_mem_of_sum_mul_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddSubgroup.exists_forall_mem_iff_single_sub_mul_mem_of_sum_mul_eq_one
    {D : Type*} [Ring D] (O : Set D) (M : AddSubgroup (Fin 2 → D))
    (hM : ∀ m ∈ M, ∀ o ∈ O, (fun i => m i * o) ∈ M)
    {ι : Type*} (t : Finset ι) (x y : ι → D)
    (hx : ∀ k ∈ t, ∃ m ∈ M, m 1 = x k)
    (hy : ∀ k ∈ t, ∀ m ∈ M, y k * m 1 ∈ O)
    (hsum : ∑ k ∈ t, x k * y k = 1) :
    ∃ u : D, ∀ v : Fin 2 → D,
      v ∈ M ↔ (Pi.single (0 : Fin 2) (v 0 - u * v 1) ∈ M ∧ ∃ m ∈ M, m 1 = v 1) := by sorry
