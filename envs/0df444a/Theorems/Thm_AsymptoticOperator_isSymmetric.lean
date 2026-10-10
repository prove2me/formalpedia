-- Prove2me | Theorems.Thm_AsymptoticOperator_isSymmetric
-- name    : AsymptoticOperator.isSymmetric
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T14:32:13.426216+00:00
-- url     : https://prove2.me/theorems/81472ca9-2f51-4a94-84f7-8662e5831cba
-- title:
--   The asymptotic operator of a symmetric loop is symmetric
-- statement:
--   Let $S:S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(t)^{\mathsf T}=S(t)$ for all $t$. Then
--   $$\langle A_Sf,g\rangle_{L^2}=\langle f,A_Sg\rangle_{L^2}\qquad\text{for all }f,g\in W^{1,2}(S^1,\mathbb{R}^{2n}).$$
-- source:
--   Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, §3.2, p. 55

import Definitions.Def_AsymptoticOperator_Setting

namespace AsymptoticOperator

open ConleyZehnder

/-- Wendl §3.2, p. 55: for a loop of symmetric matrices, `A_S` is symmetric:
`⟨A_S f, g⟩ = ⟨f, A_S g⟩` for `f, g ∈ W^{1,2}`. -/
theorem isSymmetric {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S) :
    (asymptoticOperator S).IsFormalAdjoint (asymptoticOperator S) := by sorry

end AsymptoticOperator
