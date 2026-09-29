-- Prove2me | Theorems.Thm_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact
-- name    : AutomorphicForm.ComplexIwasawa.exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/ded2bbb6-8127-5ccf-a3fb-0537a44244bc
-- title:
--   Uniform bound for area integrals of rad_ℂ^{-κ}
-- statement:
--   For a complex $2\times 2$ matrix $g$ and $z\in\mathbb C$ write $\mathrm{botP}(g,z)=g_{00}+z\,g_{10}$, $\mathrm{botQ}(g,z)=g_{01}+z\,g_{11}$ and $\mathrm{rad}_{\mathbb C}(g,z)=\sqrt{\lvert \mathrm{botP}(g,z)\rvert^{2}+\lvert \mathrm{botQ}(g,z)\rvert^{2}}$, the square root of the sum of the squared absolute values of these two linear forms in $z$ (indices being those of `Fin 2`). The data are a set $\mathcal G$ of complex $2\times 2$ matrices, assumed compact, with $\det g\neq 0$ for every $g\in\mathcal G$, together with two real numbers $\kappa_0,\kappa_1$ subject to $2<\kappa_0$. The assertion is the existence of a single real constant $M>0$ such that for every $g\in\mathcal G$ and every real $\kappa$ with $\kappa_0\le\kappa\le\kappa_1$ the function $z\mapsto \mathrm{rad}_{\mathbb C}(g,z)^{-\kappa}$ (real power) is integrable on $\mathbb C$ for its Lebesgue (area) measure and its integral satisfies $\int_{\mathbb C}\mathrm{rad}_{\mathbb C}(g,z)^{-\kappa}\,dz\le M$. Thus both integrability and the bound hold uniformly in $g$ over the compact set and in $\kappa$ over the interval $[\kappa_0,\kappa_1]$, the constant $M$ depending only on $\mathcal G$, $\kappa_0$ and $\kappa_1$.
--
--   This is the basic convergence estimate for the archimedean weight factor attached to the complex Iwasawa decomposition: away from the degenerate locus $\det g=0$ the quantity $\mathrm{rad}_{\mathbb C}(g,z)^{2}$ grows like $1+\lVert z\rVert^{2}$, uniformly over a compact set of matrices, so exponents $\kappa>2$ give convergent area integrals. It is used to obtain the polynomial decay of the Fourier integrals of $z\mapsto \mathrm{rad}_{\mathbb C}(g,z)^{-\kappa}$ in [`AutomorphicForm.ComplexIwasawa.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact`](thm.html#AutomorphicForm.ComplexIwasawa.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.lean

import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Topology.Compactness.Compact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm.ComplexIwasawa
open scoped ContDiff

theorem AutomorphicForm.ComplexIwasawa.exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (_h𝒢 : IsCompact 𝒢) (_hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (κ₀ κ₁ : ℝ) (_hκ₀ : 2 < κ₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ g ∈ 𝒢, ∀ κ : ℝ, κ₀ ≤ κ → κ ≤ κ₁ →
      Integrable (fun z : ℂ => radC g z ^ (-κ)) ∧ ∫ z : ℂ, radC g z ^ (-κ) ≤ M := by sorry
