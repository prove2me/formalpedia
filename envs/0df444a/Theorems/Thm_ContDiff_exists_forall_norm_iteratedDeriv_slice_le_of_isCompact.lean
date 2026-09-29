-- Prove2me | Theorems.Thm_ContDiff_exists_forall_norm_iteratedDeriv_slice_le_of_isCompact
-- name    : ContDiff.exists_forall_norm_iteratedDeriv_slice_le_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/482ec8d0-5e78-51b1-94cb-65ebeec3c45e
-- title:
--   Uniform bounds on slice derivatives of a smooth family
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $F$ a real normed space, and let $\Psi : E \to \mathbb{R} \to F$ be a family of maps such that the associated map $(a,u) \mapsto \Psi(a)(u)$ on $E \times \mathbb{R}$ is of class $C^\infty$ (Lean's `ContDiff ℝ (⊤ : ℕ∞)`). Let $S \subseteq E$ be compact, let $R$ be a real number, and let $N$ be a natural number. The assertion is a conjunction. First, for every $a \in E$ the slice $\Psi(a) : \mathbb{R} \to F$ is of class $C^N$. Second, there exists a constant $C \ge 0$ such that for all $a \in S$, all $u$ in the interval $[-R, R]$, and all $n \le N$, the $n$-th iterated derivative satisfies $\|\mathrm{iteratedDeriv}_n(\Psi(a))(u)\| \le C$, the single constant $C$ being uniform in $a$, $u$ and $n$. No sign condition is imposed on $R$; if $R < 0$ the interval $[-R,R]$ is empty and the bound is vacuous.
--
--   This is the standard statement that a smooth family of functions of one real variable has, on a compact parameter set and a compact interval, derivatives up to a fixed order bounded by one constant. It serves as the amplitude input to an estimate for Iwasawa-type integrals, being cited by [`AutomorphicForm.exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization`](thm.html#AutomorphicForm.exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ContDiff_exists_forall_norm_iteratedDeriv_slice_le_of_isCompact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ContDiff.exists_forall_norm_iteratedDeriv_slice_le_of_isCompact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : E → ℝ → F) (hΨ : ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => Ψ p.1 p.2))
    (S : Set E) (hS : IsCompact S) (R : ℝ) (N : ℕ) :
    (∀ a : E, ContDiff ℝ N (Ψ a)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ S, ∀ u ∈ Set.Icc (-R) R, ∀ n ≤ N, ‖iteratedDeriv n (Ψ a) u‖ ≤ C := by sorry
