-- Prove2me | Theorems.Thm_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul
-- name    : AddMonoidHom.sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/02964f11-426d-54db-8c10-2fb529e468db
-- title:
--   Integer eigenvalues of a quadratic endomorphism annihilate c²-tc+1
-- statement:
--   Let $V$ be an additively written commutative group and let $m \colon V \to V$ be an additive group homomorphism. Let $t$ be an integer, and assume the quadratic relation holds pointwise on $V$: for every $T \in V$ one has $m(m(T)) - t \cdot m(T) + T = 0$, where the scalar action is that of $\mathbb{Z}$ on the abelian group $V$. Let $P \in V$ and let $c$ be an integer such that $m(P) = c \cdot P$, i.e. $P$ is an eigenvector of $m$ with integer eigenvalue $c$. The conclusion is that the integer $c^2 - tc + 1$ annihilates $P$, that is $(c^2 - t c + 1) \cdot P = 0$ in $V$. No finiteness, torsion or order hypothesis is imposed on $V$ or on $P$, and $m$ is only assumed additive, not compatible with any further structure.
--
--   This is the elementary observation that an integer eigenvalue of an endomorphism satisfying a monic integral quadratic relation must satisfy that quadratic modulo the order of the corresponding eigenvector; applied to the action of an automorphism on a torsion subgroup it constrains the eigenvalue modulo the exact order of $P$. It is used by [`WeierstrassCurve.exists_trace_of_equivOfVariableChangeEq_symm_apply_eq_val_smul`](thm.html#WeierstrassCurve.exists_trace_of_equivOfVariableChangeEq_symm_apply_eq_val_smul), where $m$ arises from an automorphism of a Weierstrass curve acting on its points and $t$ plays the role of a trace.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddMonoidHom.sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul
    {V : Type*} [AddCommGroup V] (m : V →+ V) (t : ℤ) (hm : ∀ T, m (m T) - t • m T + T = 0)
    (P : V) (c : ℤ) (hP : m P = c • P) :
    (c ^ 2 - t * c + 1) • P = 0 := by sorry
