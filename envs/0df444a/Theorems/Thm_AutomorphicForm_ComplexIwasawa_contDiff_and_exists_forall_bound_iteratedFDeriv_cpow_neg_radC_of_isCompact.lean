-- Prove2me | Theorems.Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact
-- name    : AutomorphicForm.ComplexIwasawa.contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/64d64eaa-d973-5e99-8c57-c6da0722eb5a
-- title:
--   Smoothness and uniform symbol bounds for rad_ℂ^{-u}
-- statement:
--   Let $\mathcal G$ be a set of $2\times 2$ complex matrices which is compact and on which the determinant does not vanish, let $U\subseteq\mathbb C$ be compact, and let $n\in\mathbb N$. For a matrix $g$ and $z\in\mathbb C$ write $\mathrm{botP}(g,z)=g_{00}+z\,g_{10}$, $\mathrm{botQ}(g,z)=g_{01}+z\,g_{11}$ and $\mathrm{rad}_{\mathbb C}(g,z)=\sqrt{|\mathrm{botP}(g,z)|^{2}+|\mathrm{botQ}(g,z)|^{2}}\in\mathbb R$, the square root of the sum of the squared absolute values of these two entries. The assertion is a conjunction. First, for every $g\in\mathcal G$ and every $u\in\mathbb C$ the function $z\mapsto \mathrm{rad}_{\mathbb C}(g,z)^{-u}$, formed with the principal complex power of the real number $\mathrm{rad}_{\mathbb C}(g,z)$ viewed in $\mathbb C$, is $C^{\infty}$ as a map between the real normed spaces $\mathbb C\cong\mathbb R^{2}$ and $\mathbb C$. Secondly, there is a single constant $K>0$ such that for all $g\in\mathcal G$, all $u\in U$ and all $z\in\mathbb C$ the $n$-th real iterated Fréchet derivative of that function satisfies $\bigl\|D^{n}\bigl(z\mapsto\mathrm{rad}_{\mathbb C}(g,z)^{-u}\bigr)(z)\bigr\|\le K\,\mathrm{rad}_{\mathbb C}(g,z)^{-\operatorname{Re}u}$, the right-hand side being a real power. The order $n$ is fixed, so $K$ is allowed to depend on it, and in the first clause $u$ ranges over all of $\mathbb C$ rather than only over $U$.
--
--   This is the symbol-type estimate for the weight attached to a complex place: the function $\mathrm{rad}_{\mathbb C}(g,\cdot)^{-u}$ is smooth and each of its derivatives is dominated, uniformly in $g$ and $u$ over compact sets, by the undifferentiated majorant $\mathrm{rad}_{\mathbb C}(g,\cdot)^{-\operatorname{Re}u}$. It feeds the estimate [`AutomorphicForm.ComplexIwasawa.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact`](thm.html#AutomorphicForm.ComplexIwasawa.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact), where repeated integration by parts converts such bounds into polynomial decay of the associated Fourier integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean

import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Topology.Compactness.Compact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm.ComplexIwasawa
open scoped ContDiff

theorem AutomorphicForm.ComplexIwasawa.contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (_h𝒢 : IsCompact 𝒢) (_hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (_hU : IsCompact U) (n : ℕ) :
    (∀ g ∈ 𝒢, ∀ u : ℂ, ContDiff ℝ ∞ (fun z : ℂ => ((radC g z : ℂ) ^ (-u)))) ∧
    ∃ K : ℝ, 0 < K ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) z‖ ≤ K * radC g z ^ (-u.re) := by sorry
