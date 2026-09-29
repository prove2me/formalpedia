-- Prove2me | Theorems.Thm_AutomorphicForm_mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet
-- name    : AutomorphicForm.mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/840a38e2-bfaa-59f8-92c0-e63d6819a5dc
-- title:
--   Diagonal units of an integral upper-triangular matrix lie in R
-- statement:
--   Let $A$ be a commutative ring and let $R \subseteq A$ be a subset closed under multiplication, in the sense that $a \cdot b \in R$ whenever $a, b \in R$. Let $M \in \mathrm{GL}_2(A)$, and let $\zeta, a \in A^\times$ be units such that the underlying matrix of $M$ satisfies $M_{10} = 0$, $M_{11} = \zeta$ and $M_{00} = a\zeta$ (the entry $M_{01}$ is unconstrained). Assume further that $M$ lies in [`AutomorphicForm.integralUnitsSet R`](def/AutomorphicForm_LocalOrbitalBase.html#L33), i.e. every entry of the matrix of $M$ lies in $R$ and every entry of the matrix of $M^{-1}$ lies in $R$. The conclusion is the conjunction of two pairs of memberships: the images in $A$ of $\zeta$ and of $\zeta^{-1}$ both lie in $R$, and the images in $A$ of $a$ and of $a^{-1}$ both lie in $R$. Note that $R$ is not required to contain $1$, to be closed under addition, or to be a subring.
--
--   An elementary matrix lemma isolating the statement that, for an upper-triangular element of $\mathrm{GL}_2(A)$ whose diagonal is $(a\zeta, \zeta)$ with $a, \zeta$ units, integrality of $M$ and $M^{-1}$ forces the diagonal ratios and their inverses to be integral. It is used in the analysis of the support of the unipotent term in the twisted setting, where $A$ is a semi-local algebra (or a local field) and $R$ its ring of integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet
    {A : Type*} [CommRing A] (R : Set A) (hR : ∀ a ∈ R, ∀ b ∈ R, a * b ∈ R)
    (M : GL (Fin 2) A) (ζ a : Aˣ)
    (h10 : (M : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (h11 : (M : Matrix (Fin 2) (Fin 2) A) 1 1 = ζ)
    (h00 : (M : Matrix (Fin 2) (Fin 2) A) 0 0 = a * ζ)
    (hM : M ∈ AutomorphicForm.integralUnitsSet R) :
    ((ζ : A) ∈ R ∧ ((ζ⁻¹ : Aˣ) : A) ∈ R) ∧ ((a : A) ∈ R ∧ ((a⁻¹ : Aˣ) : A) ∈ R) := by sorry
