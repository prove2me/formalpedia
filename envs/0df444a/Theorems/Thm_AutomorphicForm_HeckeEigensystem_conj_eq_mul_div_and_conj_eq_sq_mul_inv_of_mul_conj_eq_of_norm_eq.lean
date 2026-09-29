-- Prove2me | Theorems.Thm_AutomorphicForm_HeckeEigensystem_conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq
-- name    : AutomorphicForm.HeckeEigensystem.conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/160bfd61-ba17-5d31-b51f-8aa598b4c603
-- title:
--   Conjugates of a,b when ā b=c̄ a and ‖b‖=c
-- statement:
--   Let $a,b$ be complex numbers and let $c$ be a real number with $0<c$. Assume two hypotheses: first, $a\cdot\overline{b}=c\cdot\overline{a}$, where $c$ is regarded as a complex number via the coercion $\mathbb{R}\to\mathbb{C}$ and the conjugation is `starRingEnd ℂ`; second, $\|b\|=c$, the norm being the usual absolute value on $\mathbb{C}$. The conclusion is the conjunction of two identities in $\mathbb{C}$: $\overline{a}=c\cdot(a/b)$ and $\overline{b}=c^{2}\cdot b^{-1}$. Note that division and inversion are the total operations of Mathlib's field structure on $\mathbb{C}$; under the hypotheses $b\neq 0$ automatically (since $\|b\|=c>0$), so both identities have their expected meaning, although the statement as formalised does not record $b\neq 0$ as part of its conclusion.
--
--   An elementary identity in $\mathbb{C}$: from $b\overline{b}=\|b\|^{2}$ one reads off $\overline{b}$, and then the covariance relation $a\overline{b}=c\overline{a}$ determines $\overline{a}$. It is applied with $(a,b,c)$ a pair of Hecke eigenvalues together with a positive power of a norm, to rewrite the complex conjugate of an eigenvalue table in terms of the table itself; it is used in [`AutomorphicForm.table_mem_box_of_mem_cuspClasses_siegel`](thm.html#AutomorphicForm.table_mem_box_of_mem_cuspClasses_siegel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_HeckeEigensystem_conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq.lean

import Mathlib.Analysis.Complex.Norm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.HeckeEigensystem.conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq
    (a b : ℂ) (c : ℝ) (hc : 0 < c)
    (h1 : a * starRingEnd ℂ b = (c : ℂ) * starRingEnd ℂ a) (h2 : ‖b‖ = c) :
    starRingEnd ℂ a = (c : ℂ) * (a / b) ∧ starRingEnd ℂ b = (c : ℂ) ^ 2 * b⁻¹ := by sorry
