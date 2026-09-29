-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one
-- name    : AutomorphicForm.exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/58b0da06-4f0a-516a-b103-4215f9da759f
-- title:
--   Continuous matrix representations separate points of archimedean row-isometry groups
-- statement:
--   Let $F$ be a number field. For each infinite place $w$ of $F$ write $F_w$ for the completion `w.Completion` and consider the group `rowIsometrySubgroup₀ F_w`, a subgroup of $\mathrm{GL}_2(F_w)$ defined in the same module as the row-isometry group `rowIsometrySubgroup`, whose members are the $k \in \mathrm{GL}_2(K)$ with $\|\det k\| = 1$ and $\|x k_{00} + y k_{10}\|^2 + \|x k_{01} + y k_{11}\|^2 = \|x\|^2 + \|y\|^2$ for all $x, y \in K$. Let $\kappa$ be an element of the product group $\prod_{w \mid \infty} \,$`rowIsometrySubgroup₀ F_w`, taken over all infinite places, and assume $\kappa \neq 1$. The assertion is that there exist a natural number $n$ and a monoid homomorphism $\rho$ from this product group to the multiplicative monoid of $n \times n$ complex matrices (not to $\mathrm{GL}_n(\mathbb{C})$) such that $\rho$ is continuous for the product topology on the source and the usual topology on matrices, and $\rho(\kappa) \neq 1$. Thus the continuous finite-dimensional matrix representations of the product of the archimedean row-isometry groups separate the identity from any other element.
--
--   This is the point-separation property of the continuous finite-dimensional representations of the archimedean row-isometry group $\prod_{w\mid\infty}$`rowIsometrySubgroup₀ F_w`, the archimedean frame acting on automorphic forms; the classical content is that the defining two-dimensional representation of $\mathrm{SO}(2)$, resp. $\mathrm{SU}(2)$, is faithful. It feeds the density statement for $K$-finite vectors in the cuspidal carrier, namely [`AutomorphicForm.CuspidalSpectrum.exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one
    (F : Type) [Field F] [NumberField F]
    (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (hκ : κ ≠ 1) :
    ∃ (n : ℕ) (ρ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* Matrix (Fin n) (Fin n) ℂ),
      Continuous ρ ∧ ρ κ ≠ 1 := by sorry
